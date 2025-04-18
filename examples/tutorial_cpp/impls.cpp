#include "generated.h"
#include <string>

using namespace rust::crate;

template <typename T> using Ref = rust::Ref<T>;
template <typename T> using RefMut = rust::RefMut<T>;

Inventory rust::Impl<Inventory>::new_empty(uint32_t space) {
  return Inventory(
      rust::ZngurCppOpaqueOwnedObject::build<cpp_inventory::Inventory>(space));
}

void rust::Impl<Inventory>::add_banana(RefMut<Inventory> self,
                                             uint32_t count) {
  self.cpp().add_banana(count);
}

void rust::Impl<Inventory>::add_item(RefMut<Inventory> self, Item item) {
  self.cpp().add_item(item.cpp());
}

Item rust::Impl<Item>::new_(Ref<rust::Str> name, uint32_t size) {
  return Item(rust::ZngurCppOpaqueOwnedObject::build<cpp_inventory::Item>(
      cpp_inventory::Item{
          .name = ::std::string(reinterpret_cast<const char *>(name.as_ptr()),
                                name.len()),
          .size = size}));
}

rust::std::fmt::Result rust::Impl<Inventory, rust::std::fmt::Debug>::fmt(
    Ref<Inventory> self, RefMut<rust::std::fmt::Formatter> f) {
  ::std::string result = "Inventory { remaining_space: ";
  result += ::std::to_string(self.cpp().remaining_space);
  result += ", items: [";
  bool is_first = true;
  for (const auto &item : self.cpp().items) {
    if (!is_first) {
      result += ", ";
    } else {
      is_first = false;
    }
    result += "Item { name: \"";
    result += item.name;
    result += "\", size: ";
    result += ::std::to_string(item.size);
    result += " }";
  }
  result += "] }";
  return f.write_str(rust::Str::from_char_star(result.c_str()));
}
