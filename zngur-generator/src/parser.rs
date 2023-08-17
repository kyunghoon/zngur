use std::{fmt::Display, process::exit};

use ariadne::{sources, Color, Label, Report, ReportKind};
use chumsky::prelude::*;
use iter_tools::{Either, Itertools};

use crate::{
    rust::{RustPathAndGenerics, ScalarRustType},
    RustTrait, RustType, ZngurConstructor, ZngurFile, ZngurMethod, ZngurMethodReceiver, ZngurTrait,
    ZngurType,
};

pub type Span = SimpleSpan<usize>;

type ParserInput<'a> = chumsky::input::SpannedInput<Token<'a>, Span, &'a [(Token<'a>, Span)]>;

#[derive(Debug)]
pub struct ParsedZngFile<'a>(Vec<ParsedItem<'a>>);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ParsedPathStart {
    Absolute,
    Relative,
    Crate,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ParsedPath<'a> {
    start: ParsedPathStart,
    segments: Vec<&'a str>,
    span: Span,
}

impl ParsedPath<'_> {
    fn to_zngur(self, base: &[String]) -> Vec<String> {
        match self.start {
            ParsedPathStart::Absolute => self.segments.into_iter().map(|x| x.to_owned()).collect(),
            ParsedPathStart::Relative => base
                .iter()
                .map(|x| x.as_str())
                .chain(self.segments.into_iter())
                .map(|x| x.to_owned())
                .collect(),
            ParsedPathStart::Crate => ["crate"]
                .into_iter()
                .chain(self.segments)
                .map(|x| x.to_owned())
                .collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ParsedItem<'a> {
    Mod {
        path: ParsedPath<'a>,
        items: Vec<ParsedItem<'a>>,
    },
    Type {
        ty: ParsedRustType<'a>,
        items: Vec<ParsedTypeItem<'a>>,
    },
    Trait {
        tr: ParsedRustTrait<'a>,
        methods: Vec<ParsedMethod<'a>>,
    },
    Fn(ParsedMethod<'a>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ParsedConstructorArgs<'a> {
    Unit,
    Tuple(Vec<ParsedRustType<'a>>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ParsedTypeItem<'a> {
    Properties(Vec<(&'a str, usize)>),
    Constructor {
        name: &'a str,
        args: ParsedConstructorArgs<'a>,
    },
    Method(ParsedMethod<'a>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ParsedMethod<'a> {
    name: &'a str,
    receiver: ZngurMethodReceiver,
    generics: Vec<ParsedRustType<'a>>,
    inputs: Vec<ParsedRustType<'a>>,
    output: ParsedRustType<'a>,
}

impl ParsedMethod<'_> {
    fn to_zngur(self, base: &[String]) -> ZngurMethod {
        ZngurMethod {
            name: self.name.to_owned(),
            generics: self
                .generics
                .into_iter()
                .map(|x| x.to_zngur(base))
                .collect(),
            receiver: self.receiver,
            inputs: self.inputs.into_iter().map(|x| x.to_zngur(base)).collect(),
            output: self.output.to_zngur(base),
        }
    }
}

impl ParsedItem<'_> {
    fn add_to_zngur_file(self, r: &mut ZngurFile, base: &[String]) {
        match self {
            ParsedItem::Mod { path, items } => {
                let base = path.to_zngur(base);
                for item in items {
                    item.add_to_zngur_file(r, &base);
                }
            }
            ParsedItem::Type { ty, items } => {
                let mut methods = vec![];
                let mut constructors = vec![];
                let mut size = 0;
                let mut align = 0;
                let mut is_copy = false;
                for item in items {
                    match item {
                        ParsedTypeItem::Properties(p) => {
                            for (key, value) in p {
                                match key {
                                    "size" => size = value,
                                    "align" => align = value,
                                    "is_copy" => {
                                        is_copy = match value {
                                            0 => false,
                                            1 => true,
                                            _ => todo!(),
                                        };
                                    }
                                    _ => todo!(),
                                }
                            }
                        }
                        ParsedTypeItem::Constructor { name, args } => {
                            constructors.push(ZngurConstructor {
                                name: name.to_owned(),
                                inputs: match args {
                                    ParsedConstructorArgs::Unit => vec![],
                                    ParsedConstructorArgs::Tuple(t) => t
                                        .into_iter()
                                        .enumerate()
                                        .map(|(i, t)| (i.to_string(), t.to_zngur(base)))
                                        .collect(),
                                },
                            })
                        }
                        ParsedTypeItem::Method(m) => methods.push(m.to_zngur(base)),
                    }
                }
                r.types.push(ZngurType {
                    ty: ty.to_zngur(base),
                    size,
                    align,
                    is_copy,
                    methods,
                    constructors,
                });
            }
            ParsedItem::Trait { tr, methods } => r.traits.push(ZngurTrait {
                tr: tr.to_zngur(base),
                methods: methods.into_iter().map(|m| m.to_zngur(base)).collect(),
            }),
            ParsedItem::Fn(f) => r.funcs.push(f.to_zngur(base)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ParsedRustType<'a> {
    Scalar(ScalarRustType),
    Ref(Box<ParsedRustType<'a>>),
    RefMut(Box<ParsedRustType<'a>>),
    Boxed(Box<ParsedRustType<'a>>),
    Dyn(ParsedRustTrait<'a>),
    Tuple(Vec<ParsedRustType<'a>>),
    Adt(ParsedRustPathAndGenerics<'a>),
}

impl ParsedRustType<'_> {
    fn to_zngur(self, base: &[String]) -> RustType {
        match self {
            ParsedRustType::Scalar(s) => RustType::Scalar(s),
            ParsedRustType::Ref(s) => RustType::Ref(Box::new(s.to_zngur(base))),
            ParsedRustType::RefMut(s) => RustType::RefMut(Box::new(s.to_zngur(base))),
            ParsedRustType::Boxed(s) => RustType::Boxed(Box::new(s.to_zngur(base))),
            ParsedRustType::Dyn(tr) => RustType::Dyn(tr.to_zngur(base)),
            ParsedRustType::Tuple(v) => {
                RustType::Tuple(v.into_iter().map(|s| s.to_zngur(base)).collect())
            }
            ParsedRustType::Adt(s) => RustType::Adt(s.to_zngur(base)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ParsedRustTrait<'a> {
    Normal(ParsedRustPathAndGenerics<'a>),
    Fn {
        name: &'a str,
        inputs: Vec<ParsedRustType<'a>>,
        output: Box<ParsedRustType<'a>>,
    },
}

impl ParsedRustTrait<'_> {
    fn to_zngur(self, base: &[String]) -> RustTrait {
        match self {
            ParsedRustTrait::Normal(s) => RustTrait::Normal(s.to_zngur(base)),
            ParsedRustTrait::Fn {
                name,
                inputs,
                output,
            } => RustTrait::Fn {
                name: name.to_owned(),
                inputs: inputs.into_iter().map(|s| s.to_zngur(base)).collect(),
                output: Box::new(output.to_zngur(base)),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ParsedRustPathAndGenerics<'a> {
    path: ParsedPath<'a>,
    generics: Vec<ParsedRustType<'a>>,
    named_generics: Vec<(&'a str, ParsedRustType<'a>)>,
}

impl ParsedRustPathAndGenerics<'_> {
    fn to_zngur(self, base: &[String]) -> RustPathAndGenerics {
        RustPathAndGenerics {
            path: self.path.to_zngur(base),
            generics: self
                .generics
                .into_iter()
                .map(|x| x.to_zngur(base))
                .collect(),
            named_generics: self
                .named_generics
                .into_iter()
                .map(|(name, x)| (name.to_owned(), x.to_zngur(base)))
                .collect(),
        }
    }
}

impl ParsedZngFile<'_> {
    pub fn parse<T>(
        filename: &str,
        text: &str,
        then: impl for<'a> Fn(ParsedZngFile<'a>) -> T,
    ) -> T {
        let (tokens, errs) = lexer().parse(text).into_output_errors();
        let tokens = match tokens {
            Some(tokens) => tokens,
            None => {
                let errs = errs.into_iter().map(|e| e.map_token(|c| c.to_string()));
                handle_error(errs, filename, text);
                exit(0);
            }
        };
        let (ast, errs) = file_parser()
            .map_with_span(|ast, span| (ast, span))
            .parse(tokens.as_slice().spanned((text.len()..text.len()).into()))
            .into_output_errors();
        let ast = match ast {
            Some(x) => x,
            None => {
                let errs = errs.into_iter().map(|e| e.map_token(|c| c.to_string()));
                handle_error(errs, filename, text);
                exit(0);
            }
        };
        then(ast.0)
    }

    pub(crate) fn into_zngur_file(self) -> ZngurFile {
        let mut r = ZngurFile::default();
        for item in self.0 {
            item.add_to_zngur_file(&mut r, &[]);
        }
        r
    }
}

fn handle_error<'a>(errs: impl Iterator<Item = Rich<'a, String>>, filename: &str, text: &str) {
    for e in errs {
        Report::build(ReportKind::Error, filename, e.span().start)
            .with_message(e.to_string())
            .with_label(
                Label::new((filename.to_string(), e.span().into_range()))
                    .with_message(e.reason().to_string())
                    .with_color(Color::Red),
            )
            .with_labels(e.contexts().map(|(label, span)| {
                Label::new((filename.to_string(), span.into_range()))
                    .with_message(format!("while parsing this {}", label))
                    .with_color(Color::Yellow)
            }))
            .finish()
            .print(sources([(filename.to_string(), text)]))
            .unwrap();
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token<'a> {
    ColonColon,
    Arrow,
    BracketOpen,
    BracketClose,
    ParenOpen,
    ParenClose,
    BraceOpen,
    BraceClose,
    And,
    Eq,
    Comma,
    Semicolon,
    KwDyn,
    KwMod,
    KwCrate,
    KwType,
    KwTrait,
    KwFn,
    KwMut,
    Ident(&'a str),
    Number(usize),
}

impl Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::ColonColon => write!(f, "::"),
            Token::Arrow => write!(f, "->"),
            Token::BracketOpen => write!(f, "<"),
            Token::BracketClose => write!(f, ">"),
            Token::ParenOpen => write!(f, "("),
            Token::ParenClose => write!(f, ")"),
            Token::BraceOpen => write!(f, "{{"),
            Token::BraceClose => write!(f, "}}"),
            Token::And => write!(f, "&"),
            Token::Eq => write!(f, "="),
            Token::Comma => write!(f, ","),
            Token::Semicolon => write!(f, ";"),
            Token::KwDyn => write!(f, "dyn"),
            Token::KwMod => write!(f, "mod"),
            Token::KwCrate => write!(f, "crate"),
            Token::KwType => write!(f, "type"),
            Token::KwTrait => write!(f, "trait"),
            Token::KwFn => write!(f, "fn"),
            Token::KwMut => write!(f, "mut"),
            Token::Ident(i) => write!(f, "{i}"),
            Token::Number(n) => write!(f, "{n}"),
        }
    }
}

fn lexer<'src>(
) -> impl Parser<'src, &'src str, Vec<(Token<'src>, Span)>, extra::Err<Rich<'src, char, Span>>> {
    let token = choice([
        just("::").to(Token::ColonColon),
        just("->").to(Token::Arrow),
        just("<").to(Token::BracketOpen),
        just(">").to(Token::BracketClose),
        just("(").to(Token::ParenOpen),
        just(")").to(Token::ParenClose),
        just("{").to(Token::BraceOpen),
        just("}").to(Token::BraceClose),
        just("&").to(Token::And),
        just("=").to(Token::Eq),
        just(",").to(Token::Comma),
        just(";").to(Token::Semicolon),
        just("dyn").to(Token::KwDyn),
        just("mod").to(Token::KwMod),
        just("type").to(Token::KwType),
        just("trait").to(Token::KwTrait),
        just("crate").to(Token::KwCrate),
        just("fn").to(Token::KwFn),
        just("mut").to(Token::KwMut),
    ])
    .or(text::ident().map(|x| Token::Ident(x)))
    .or(text::int(10).map(|x: &str| Token::Number(x.parse().unwrap())));
    token
        .map_with_span(|tok, span| (tok, span))
        .padded()
        .repeated()
        .collect()
}

fn file_parser<'a>(
) -> impl Parser<'a, ParserInput<'a>, ParsedZngFile<'a>, extra::Err<Rich<'a, Token<'a>, Span>>> + Clone
{
    item().repeated().collect::<Vec<_>>().map(ParsedZngFile)
}

fn rust_type<'a>(
) -> impl Parser<'a, ParserInput<'a>, ParsedRustType<'a>, extra::Err<Rich<'a, Token<'a>, Span>>> + Clone
{
    let as_scalar = |s: &str, head: char| -> Option<u32> {
        let s = s.strip_prefix(head)?;
        s.parse().ok()
    };

    let scalar = select! {
        Token::Ident(c) if as_scalar(c, 'u').is_some() => ParsedRustType::Scalar(ScalarRustType::Uint(as_scalar(c, 'u').unwrap())),
        Token::Ident(c) if as_scalar(c, 'i').is_some() => ParsedRustType::Scalar(ScalarRustType::Int(as_scalar(c, 'i').unwrap())),
    };

    recursive(|parser| {
        let pg = rust_path_and_generics(parser.clone());
        let adt = pg.clone().map(ParsedRustType::Adt);

        let dyn_trait = just(Token::KwDyn)
            .ignore_then(rust_trait(parser.clone()))
            .map(ParsedRustType::Dyn);
        let boxed = just(Token::Ident("Box"))
            .then(rust_generics(parser.clone()))
            .map(|(_, x)| {
                assert_eq!(x.len(), 1);
                ParsedRustType::Boxed(Box::new(x.into_iter().next().unwrap().right().unwrap()))
            });
        let unit = just(Token::ParenOpen)
            .then(just(Token::ParenClose))
            .map(|_| ParsedRustType::Tuple(vec![]));
        let reference = just(Token::And)
            .then(parser.clone())
            .map(|x| ParsedRustType::Ref(Box::new(x.1)));
        let reference_mut = just(Token::And)
            .then(just(Token::KwMut))
            .ignore_then(parser)
            .map(|x| ParsedRustType::RefMut(Box::new(x)));
        scalar
            .or(boxed)
            .or(unit)
            .or(adt)
            .or(reference_mut)
            .or(reference)
            .or(dyn_trait)
    })
}

fn rust_generics<'a>(
    rust_type: impl Parser<'a, ParserInput<'a>, ParsedRustType<'a>, extra::Err<Rich<'a, Token<'a>, Span>>>
        + Clone,
) -> impl Parser<
    'a,
    ParserInput<'a>,
    Vec<Either<(&'a str, ParsedRustType<'a>), ParsedRustType<'a>>>,
    extra::Err<Rich<'a, Token<'a>, Span>>,
> + Clone {
    let named_generic = select! {
        Token::Ident(c) => c,
    }
    .then_ignore(just(Token::Eq))
    .then(rust_type.clone())
    .map(Either::Left);
    just(Token::ColonColon).repeated().at_most(1).ignore_then(
        named_generic
            .or(rust_type.clone().map(Either::Right))
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect::<Vec<_>>()
            .delimited_by(just(Token::BracketOpen), just(Token::BracketClose)),
    )
}

fn rust_path_and_generics<'a>(
    rust_type: impl Parser<'a, ParserInput<'a>, ParsedRustType<'a>, extra::Err<Rich<'a, Token<'a>, Span>>>
        + Clone,
) -> impl Parser<
    'a,
    ParserInput<'a>,
    ParsedRustPathAndGenerics<'a>,
    extra::Err<Rich<'a, Token<'a>, Span>>,
> + Clone {
    let generics = rust_generics(rust_type.clone());
    path()
        .then(generics.clone().repeated().at_most(1).collect::<Vec<_>>())
        .map(|x| {
            let generics = x.1.into_iter().next().unwrap_or_default();
            let (named_generics, generics) = generics.into_iter().partition_map(|x| x);
            ParsedRustPathAndGenerics {
                path: x.0,
                generics,
                named_generics,
            }
        })
}

fn fn_args<'a>(
    rust_type: impl Parser<'a, ParserInput<'a>, ParsedRustType<'a>, extra::Err<Rich<'a, Token<'a>, Span>>>
        + Clone,
) -> impl Parser<
    'a,
    ParserInput<'a>,
    (Vec<ParsedRustType<'a>>, ParsedRustType<'a>),
    extra::Err<Rich<'a, Token<'a>, Span>>,
> + Clone {
    rust_type
        .clone()
        .separated_by(just(Token::Comma))
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
        .then(
            just(Token::Arrow)
                .ignore_then(rust_type)
                .or(empty().to(ParsedRustType::Tuple(vec![]))),
        )
}

fn rust_trait<'a>(
    rust_type: impl Parser<'a, ParserInput<'a>, ParsedRustType<'a>, extra::Err<Rich<'a, Token<'a>, Span>>>
        + Clone,
) -> impl Parser<'a, ParserInput<'a>, ParsedRustTrait<'a>, extra::Err<Rich<'a, Token<'a>, Span>>> + Clone
{
    let fn_trait = select! {
        Token::Ident(c) => c,
    }
    .then(fn_args(rust_type.clone()))
    .map(|x| ParsedRustTrait::Fn {
        name: x.0,
        inputs: x.1 .0,
        output: Box::new(x.1 .1),
    });

    let rust_trait = fn_trait.or(rust_path_and_generics(rust_type).map(ParsedRustTrait::Normal));
    rust_trait
}

fn method<'a>(
) -> impl Parser<'a, ParserInput<'a>, ParsedMethod<'a>, extra::Err<Rich<'a, Token<'a>, Span>>> + Clone
{
    just(Token::KwFn)
        .ignore_then(select! {
            Token::Ident(c) => c,
        })
        .then(
            rust_type()
                .separated_by(just(Token::Comma))
                .collect::<Vec<_>>()
                .delimited_by(just(Token::BracketOpen), just(Token::BracketClose))
                .or(empty().to(vec![])),
        )
        .then(fn_args(rust_type()))
        .map(|((name, generics), args)| {
            let is_self = |c: &ParsedRustType<'_>| {
                if let ParsedRustType::Adt(c) = c {
                    c.path.start == ParsedPathStart::Relative
                        && &c.path.segments == &["self"]
                        && c.generics.is_empty()
                } else {
                    false
                }
            };
            let (inputs, receiver) = match args.0.get(0) {
                Some(x) if is_self(&x) => (args.0[1..].to_vec(), ZngurMethodReceiver::Move),
                Some(ParsedRustType::Ref(x)) if is_self(&x) => {
                    (args.0[1..].to_vec(), ZngurMethodReceiver::Ref)
                }
                Some(ParsedRustType::RefMut(x)) if is_self(&x) => {
                    (args.0[1..].to_vec(), ZngurMethodReceiver::RefMut)
                }
                _ => (args.0, ZngurMethodReceiver::Static),
            };
            ParsedMethod {
                name,
                receiver,
                generics,
                inputs,
                output: args.1,
            }
        })
}

fn type_item<'a>(
) -> impl Parser<'a, ParserInput<'a>, ParsedItem<'a>, extra::Err<Rich<'a, Token<'a>, Span>>> + Clone
{
    fn inner_item<'a>(
    ) -> impl Parser<'a, ParserInput<'a>, ParsedTypeItem<'a>, extra::Err<Rich<'a, Token<'a>, Span>>>
           + Clone {
        let property_item = (select! {
            Token::Ident(c) => c,
        })
        .then_ignore(just(Token::Eq))
        .then(select! {
            Token::Number(c) => c,
        });
        let properties = just(Token::Ident("properties"))
            .ignore_then(
                property_item
                    .separated_by(just(Token::Comma))
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::ParenOpen), just(Token::ParenClose)),
            )
            .map(|x| ParsedTypeItem::Properties(x));
        let constructor_args = rust_type()
            .separated_by(just(Token::Comma))
            .collect::<Vec<_>>()
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(ParsedConstructorArgs::Tuple)
            .or(empty().to(ParsedConstructorArgs::Unit));
        let constructor = just(Token::Ident("constructor")).ignore_then(
            (select! {
                Token::Ident(c) => c,
            })
            .then(constructor_args)
            .map(|(name, args)| ParsedTypeItem::Constructor { name, args }),
        );
        properties
            .or(constructor)
            .or(method().map(ParsedTypeItem::Method))
            .then_ignore(just(Token::Semicolon))
    }
    just(Token::KwType)
        .ignore_then(rust_type())
        .then(
            inner_item()
                .repeated()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::BraceOpen), just(Token::BraceClose)),
        )
        .map(|(ty, items)| ParsedItem::Type { ty, items })
}

fn trait_item<'a>(
) -> impl Parser<'a, ParserInput<'a>, ParsedItem<'a>, extra::Err<Rich<'a, Token<'a>, Span>>> + Clone
{
    just(Token::KwTrait)
        .ignore_then(rust_trait(rust_type()))
        .then(
            method()
                .then_ignore(just(Token::Semicolon))
                .repeated()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::BraceOpen), just(Token::BraceClose)),
        )
        .map(|(tr, methods)| ParsedItem::Trait { tr, methods })
}

fn fn_item<'a>(
) -> impl Parser<'a, ParserInput<'a>, ParsedItem<'a>, extra::Err<Rich<'a, Token<'a>, Span>>> + Clone
{
    method()
        .then_ignore(just(Token::Semicolon))
        .map(ParsedItem::Fn)
}

fn item<'a>(
) -> impl Parser<'a, ParserInput<'a>, ParsedItem<'a>, extra::Err<Rich<'a, Token<'a>, Span>>> + Clone
{
    recursive(|item| {
        just(Token::KwMod)
            .ignore_then(path())
            .then(
                item.repeated()
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::BraceOpen), just(Token::BraceClose)),
            )
            .map(|(path, items)| ParsedItem::Mod { path, items })
            .or(type_item())
            .or(trait_item())
            .or(fn_item())
    })
}

fn path<'a>(
) -> impl Parser<'a, ParserInput<'a>, ParsedPath<'a>, extra::Err<Rich<'a, Token<'a>, Span>>> + Clone
{
    let start = choice([
        just(Token::ColonColon).to(ParsedPathStart::Absolute),
        just(Token::KwCrate).to(ParsedPathStart::Crate),
    ])
    .or(empty().to(ParsedPathStart::Relative));
    start
        .then(
            (select! {
                Token::Ident(c) => c,
            })
            .separated_by(just(Token::ColonColon))
            .at_least(1)
            .collect::<Vec<_>>(),
        )
        .or(just(Token::KwCrate).to((ParsedPathStart::Crate, vec![])))
        .map_with_span(|(start, segments), span| ParsedPath {
            start,
            segments,
            span,
        })
}
