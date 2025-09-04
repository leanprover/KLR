#include "../klr/fromNKI.hpp"
#include <cassert>
#include <iostream>

using namespace Trace;

// Helper to create Terms
Term makeBool(bool value) {
    Term t;
    t.kind = Term::Bool;
    t.data = value;
    return t;
}

Term makeInt(int value) {
    Term t;
    t.kind = Term::Int;
    t.data = value;
    return t;
}

Term makeFloat(float value) {
    Term t;
    t.kind = Term::Float;
    t.data = value;
    return t;
}

Term makeString(const std::string& value) {
    Term t;
    t.kind = Term::String;
    t.data = value;
    return t;
}

Term makeNone() {
    Term t;
    t.kind = Term::None;
    t.data = std::monostate{};
    return t;
}

Term makeList(const std::vector<Term>& items) {
    Term t;
    t.kind = Term::List;
    t.data = items;
    return t;
}

Term makeTuple(const std::vector<Term>& items) {
    Term t;
    t.kind = Term::Tuple;
    t.data = items;
    return t;
}

void test_bool_conversion() {
    std::cout << "Testing bool conversion..." << std::endl;
    
    auto result = FromNKI<bool>::fromNKI(makeBool(true));
    assert(is_ok(result));
    assert(get_ok(result) == true);
    
    result = FromNKI<bool>::fromNKI(makeBool(false));
    assert(is_ok(result));
    assert(get_ok(result) == false);
    
    // Error case
    result = FromNKI<bool>::fromNKI(makeInt(42));
    assert(!is_ok(result));
}

void test_int_conversion() {
    std::cout << "Testing int conversion..." << std::endl;
    
    auto result = FromNKI<int>::fromNKI(makeInt(42));
    assert(is_ok(result));
    assert(get_ok(result) == 42);
    
    // Bool to int
    result = FromNKI<int>::fromNKI(makeBool(true));
    assert(is_ok(result));
    assert(get_ok(result) == 1);
    
    result = FromNKI<int>::fromNKI(makeBool(false));
    assert(is_ok(result));
    assert(get_ok(result) == 0);
    
    // Error case
    result = FromNKI<int>::fromNKI(makeString("hello"));
    assert(!is_ok(result));
}

void test_float_conversion() {
    std::cout << "Testing float conversion..." << std::endl;
    
    auto result = FromNKI<float>::fromNKI(makeFloat(3.14f));
    assert(is_ok(result));
    assert(get_ok(result) == 3.14f);
    
    // Int to float
    result = FromNKI<float>::fromNKI(makeInt(42));
    assert(is_ok(result));
    assert(get_ok(result) == 42.0f);
    
    // Bool to float
    result = FromNKI<float>::fromNKI(makeBool(true));
    assert(is_ok(result));
    assert(get_ok(result) == 1.0f);
}

void test_string_conversion() {
    std::cout << "Testing string conversion..." << std::endl;
    
    auto result = FromNKI<std::string>::fromNKI(makeString("hello"));
    assert(is_ok(result));
    assert(get_ok(result) == "hello");
    
    // Error case
    result = FromNKI<std::string>::fromNKI(makeInt(42));
    assert(!is_ok(result));
}

void test_vector_conversion() {
    std::cout << "Testing vector conversion..." << std::endl;
    
    std::vector<Term> items = {makeInt(1), makeInt(2), makeInt(3)};
    auto result = FromNKI<std::vector<int>>::fromNKI(makeList(items));
    assert(is_ok(result));
    auto vec = get_ok(result);
    assert(vec.size() == 3);
    assert(vec[0] == 1 && vec[1] == 2 && vec[2] == 3);
    
    // Tuple should also work
    result = FromNKI<std::vector<int>>::fromNKI(makeTuple(items));
    assert(is_ok(result));
    
    // Error case - wrong item type
    std::vector<Term> bad_items = {makeInt(1), makeString("bad")};
    result = FromNKI<std::vector<int>>::fromNKI(makeList(bad_items));
    assert(!is_ok(result));
}

void test_optional_conversion() {
    std::cout << "Testing optional conversion..." << std::endl;
    
    // None case
    auto result = FromNKI<std::optional<int>>::fromNKI(makeNone());
    assert(is_ok(result));
    assert(!get_ok(result).has_value());
    
    // Value case
    result = FromNKI<std::optional<int>>::fromNKI(makeInt(42));
    assert(is_ok(result));
    assert(get_ok(result).has_value());
    assert(get_ok(result).value() == 42);
}

void test_pair_conversion() {
    std::cout << "Testing pair conversion..." << std::endl;
    
    std::vector<Term> items = {makeInt(1), makeString("hello")};
    auto result = FromNKI<std::pair<int, std::string>>::fromNKI(makeList(items));
    assert(is_ok(result));
    auto pair = get_ok(result);
    assert(pair.first == 1);
    assert(pair.second == "hello");
    
    // Error case - wrong size
    std::vector<Term> bad_items = {makeInt(1)};
    result = FromNKI<std::pair<int, std::string>>::fromNKI(makeList(bad_items));
    assert(!is_ok(result));
}

void test_variant_conversion() {
    std::cout << "Testing variant conversion..." << std::endl;
    
    // First type matches
    auto result = FromNKI<std::variant<int, std::string>>::fromNKI(makeInt(42));
    assert(is_ok(result));
    auto var = get_ok(result);
    assert(std::holds_alternative<int>(var));
    assert(std::get<int>(var) == 42);
    
    // Second type matches
    result = FromNKI<std::variant<int, std::string>>::fromNKI(makeString("hello"));
    assert(is_ok(result));
    var = get_ok(result);
    assert(std::holds_alternative<std::string>(var));
    assert(std::get<std::string>(var) == "hello");
    
    // Neither matches
    result = FromNKI<std::variant<int, std::string>>::fromNKI(makeFloat(3.14f));
    assert(!is_ok(result));
}

void test_shape_conversion() {
    std::cout << "Testing shape conversion..." << std::endl;
    
    std::vector<Term> dims = {makeInt(2), makeInt(3), makeInt(4)};
    auto result = FromNKI<klr::Shape>::fromNKI(makeList(dims));
    assert(is_ok(result));
    auto shape = get_ok(result);
    assert(shape.parDim == 2);
    assert(shape.freeDims.size() == 2);
    auto it = shape.freeDims.begin();
    assert(*it == 3);
    ++it;
    assert(*it == 4);
    
    // Error case - empty list
    result = FromNKI<klr::Shape>::fromNKI(makeList({}));
    assert(!is_ok(result));
}

void test_kindStr() {
    std::cout << "Testing kindStr..." << std::endl;
    
    assert(makeBool(true).kindStr() == "Bool");
    assert(makeInt(42).kindStr() == "Int");
    assert(makeFloat(3.14f).kindStr() == "Float");
    assert(makeString("hello").kindStr() == "String");
    assert(makeNone().kindStr() == "None");
    assert(makeList({}).kindStr() == "List");
    assert(makeTuple({}).kindStr() == "Tuple");
}

int main() {
    test_bool_conversion();
    test_int_conversion();
    test_float_conversion();
    test_string_conversion();
    test_vector_conversion();
    test_optional_conversion();
    test_pair_conversion();
    test_variant_conversion();
    test_shape_conversion();
    test_kindStr();
    
    std::cout << "All tests passed!" << std::endl;
    return 0;
}