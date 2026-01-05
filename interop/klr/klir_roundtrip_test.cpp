/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Round trip tests for KLIR serialization/deserialization functions
*/

#include <iostream>
#include <cstdio>
#include <cstring>
#include <vector>
#include <cassert>
#include <cmath>
#include "klir_common.hpp"
#include "klir_serde.hpp"

using namespace std;
using namespace klr;

// Helper function to create a temporary file for testing
FILE *create_temp_file() { return tmpfile(); }

// Test helper to check if two floats are approximately equal
bool float_equal(float a, float b, float epsilon = 1e-6f) {
  return fabs(a - b) < epsilon;
}

// Test Option<Bool> round trip
bool test_option_bool_roundtrip() {
  cout << "Testing Option<Bool> round trip... ";

  vector<Option<Bool>> test_values = {
      Option<Bool>(),     // None
      Option<Bool>(true), // Some(true)
      Option<Bool>(false) // Some(false)
  };

  for (const Option<Bool> &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    // Serialize
    if (!Option_Bool_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    Option<Bool> deserialized = Option_Bool_des(temp);

    fclose(temp);

    if (original.has_value != deserialized.has_value) {
      cout << "FAILED (has_value mismatch: expected " << original.has_value
           << ", got " << deserialized.has_value << ")" << endl;
      return false;
    }

    if (original.has_value && original.value != deserialized.value) {
      cout << "FAILED (value mismatch: expected " << original.value << ", got "
           << deserialized.value << ")" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Option<Nat> round trip
bool test_option_nat_roundtrip() {
  cout << "Testing Option<Nat> round trip... ";

  vector<Option<Nat>> test_values = {
      Option<Nat>(),           // None
      Option<Nat>(0),          // Some(0)
      Option<Nat>(42),         // Some(42)
      Option<Nat>(4294967295U) // Some(max u32)
  };

  for (const Option<Nat> &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    // Serialize
    if (!Option_Nat_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    Option<Nat> deserialized = Option_Nat_des(temp);

    fclose(temp);

    if (original.has_value != deserialized.has_value) {
      cout << "FAILED (has_value mismatch: expected " << original.has_value
           << ", got " << deserialized.has_value << ")" << endl;
      return false;
    }

    if (original.has_value && original.value != deserialized.value) {
      cout << "FAILED (value mismatch: expected " << original.value << ", got "
           << deserialized.value << ")" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Option<String> round trip
bool test_option_string_roundtrip() {
  cout << "Testing Option<String> round trip... ";

  vector<Option<String>> test_values = {
      Option<String>(),                // None
      Option<String>(""),              // Some("")
      Option<String>("hello"),         // Some("hello")
      Option<String>("Hello, World!"), // Some("Hello, World!")
      Option<String>("Unicode: αβγδε") // Some with unicode
  };

  for (const Option<String> &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    // Serialize
    if (!Option_String_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    Option<String> deserialized = Option_String_des(temp);

    fclose(temp);

    if (original.has_value != deserialized.has_value) {
      cout << "FAILED (has_value mismatch: expected " << original.has_value
           << ", got " << deserialized.has_value << ")" << endl;
      return false;
    }

    if (original.has_value && original.value != deserialized.value) {
      cout << "FAILED (value mismatch: expected \"" << original.value
           << "\", got \"" << deserialized.value << "\")" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test List<Bool> round trip
bool test_list_bool_roundtrip() {
  cout << "Testing List<Bool> round trip... ";

  vector<List<Bool>> test_values = {
      {},                         // Empty list
      {true},                     // Single element
      {false},                    // Single false
      {true, false, true, false}, // Multiple elements
      {true, true, true}          // All true
  };

  for (const List<Bool> &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    // Serialize
    if (!List_Bool_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    List<Bool> deserialized = List_Bool_des(temp);

    fclose(temp);

    if (original.size() != deserialized.size()) {
      cout << "FAILED (size mismatch: expected " << original.size() << ", got "
           << deserialized.size() << ")" << endl;
      return false;
    }

    auto orig_it = original.begin();
    auto deser_it = deserialized.begin();
    size_t i = 0;
    while (orig_it != original.end() && deser_it != deserialized.end()) {
      if (*orig_it != *deser_it) {
        cout << "FAILED (element " << i << " mismatch: expected " << *orig_it
             << ", got " << *deser_it << ")" << endl;
        return false;
      }
      ++orig_it;
      ++deser_it;
      ++i;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Option<List<Nat>> round trip
bool test_option_list_nat_roundtrip() {
  cout << "Testing Option<List<Nat>> round trip... ";

  vector<Option<List<Nat>>> test_values = {
      Option<List<Nat>>(),                   // None
      Option<List<Nat>>(List<Nat>{}),        // Some(empty list)
      Option<List<Nat>>(List<Nat>{1, 2, 3}), // Some(list with elements)
      Option<List<Nat>>(
          List<Nat>{0, 42, 4294967295U}) // Some(list with edge values)
  };

  for (const Option<List<Nat>> &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    // Serialize
    if (!Option_List_Nat_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    Option<List<Nat>> deserialized = Option_List_Nat_des(temp);

    fclose(temp);

    if (original.has_value != deserialized.has_value) {
      cout << "FAILED (has_value mismatch: expected " << original.has_value
           << ", got " << deserialized.has_value << ")" << endl;
      return false;
    }

    if (original.has_value) {
      if (original.value.size() != deserialized.value.size()) {
        cout << "FAILED (size mismatch: expected " << original.value.size()
             << ", got " << deserialized.value.size() << ")" << endl;
        return false;
      }

      auto orig_it = original.value.begin();
      auto deser_it = deserialized.value.begin();
      size_t i = 0;
      while (orig_it != original.value.end() &&
             deser_it != deserialized.value.end()) {
        if (*orig_it != *deser_it) {
          cout << "FAILED (element " << i << " mismatch: expected " << *orig_it
               << ", got " << *deser_it << ")" << endl;
          return false;
        }
        ++orig_it;
        ++deser_it;
        ++i;
      }
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test List<String> round trip
bool test_list_string_roundtrip() {
  cout << "Testing List<String> round trip... ";

  vector<List<String>> test_values = {
      {},                                  // Empty list
      {"hello"},                           // Single element
      {"", "world"},                       // Empty string and normal string
      {"hello", "world", "test"},          // Multiple elements
      {"Unicode: αβγδε", "Special: !@#$%"} // Unicode and special chars
  };

  for (const List<String> &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    // Serialize
    if (!List_String_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    List<String> deserialized = List_String_des(temp);

    fclose(temp);

    if (original.size() != deserialized.size()) {
      cout << "FAILED (size mismatch: expected " << original.size() << ", got "
           << deserialized.size() << ")" << endl;
      return false;
    }

    auto orig_it = original.begin();
    auto deser_it = deserialized.begin();
    size_t i = 0;
    while (orig_it != original.end() && deser_it != deserialized.end()) {
      if (*orig_it != *deser_it) {
        cout << "FAILED (element " << i << " mismatch: expected \"" << *orig_it
             << "\", got \"" << *deser_it << "\")" << endl;
        return false;
      }
      ++orig_it;
      ++deser_it;
      ++i;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Pos round trip (a simple struct)
bool test_pos_roundtrip() {
  cout << "Testing Pos round trip... ";

  vector<Ptr<Pos>> test_values;

  // Basic position
  auto pos1 = ptr<Pos>();
  pos1->line = 1;
  pos1->column = 1;
  pos1->lineEnd = Option<Nat>();
  pos1->columnEnd = Option<Nat>();
  pos1->filename = Option<String>();
  test_values.push_back(pos1);

  // With line/column end
  auto pos2 = ptr<Pos>();
  pos2->line = 10;
  pos2->column = 20;
  pos2->lineEnd = Option<Nat>(15);
  pos2->columnEnd = Option<Nat>(25);
  pos2->filename = Option<String>();
  test_values.push_back(pos2);

  // With filename
  auto pos3 = ptr<Pos>();
  pos3->line = 5;
  pos3->column = 8;
  pos3->lineEnd = Option<Nat>();
  pos3->columnEnd = Option<Nat>();
  pos3->filename = Option<String>("test.txt");
  test_values.push_back(pos3);

  // Full position
  auto pos4 = ptr<Pos>();
  pos4->line = 100;
  pos4->column = 200;
  pos4->lineEnd = Option<Nat>(150);
  pos4->columnEnd = Option<Nat>(250);
  pos4->filename = Option<String>("main.cpp");
  test_values.push_back(pos4);

  for (const Ptr<Pos> &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    // Serialize
    if (!Pos_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    Ptr<Pos> deserialized = Pos_des(temp);

    fclose(temp);

    if (original->line != deserialized->line ||
        original->column != deserialized->column ||
        original->lineEnd.has_value != deserialized->lineEnd.has_value ||
        original->columnEnd.has_value != deserialized->columnEnd.has_value ||
        original->filename.has_value != deserialized->filename.has_value) {
      cout << "FAILED (basic field mismatch)" << endl;
      return false;
    }

    if (original->lineEnd.has_value &&
        original->lineEnd.value != deserialized->lineEnd.value) {
      cout << "FAILED (lineEnd mismatch)" << endl;
      return false;
    }

    if (original->columnEnd.has_value &&
        original->columnEnd.value != deserialized->columnEnd.value) {
      cout << "FAILED (columnEnd mismatch)" << endl;
      return false;
    }

    if (original->filename.has_value &&
        original->filename.value != deserialized->filename.value) {
      cout << "FAILED (filename mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Memory enum round trip
bool test_memory_roundtrip() {
  cout << "Testing Memory enum round trip... ";

  vector<Memory> test_values = {Memory::hbm,        Memory::sbuf,
                                Memory::psum,       Memory::reg,
                                Memory::shared_hbm, Memory::private_hbm};

  for (const Memory &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    // Serialize
    if (!Memory_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    Memory deserialized = Memory_des(temp);

    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (value mismatch: expected " << (int)original << ", got "
           << (int)deserialized << ")" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test simple Operator round trip (RegisterMove)
bool test_operator_register_move_roundtrip() {
  cout << "Testing Operator (RegisterMove) round trip... ";

  // Create a simple RegisterMove operator
  auto regMove = ptr<RegisterMove>();
  regMove->dst = "r1";
  regMove->imm = 42;

  auto operatorWrapper = ptr<OperatorRegisterMoveWrapper>();
  operatorWrapper->op = regMove;

  FILE *temp = create_temp_file();
  if (!temp) {
    cout << "FAILED (could not create temp file)" << endl;
    return false;
  }

  // Serialize
  if (!Operator_ser(temp, operatorWrapper)) {
    cout << "FAILED (serialization failed)" << endl;
    fclose(temp);
    return false;
  }

  // Reset file position
  rewind(temp);

  // Deserialize
  Ptr<Operator> deserialized = Operator_des(temp);

  fclose(temp);

  // Check that we got the right type back
  if (deserialized->tag != Operator::Tag::registerMove) {
    cout << "FAILED (wrong operator tag)" << endl;
    return false;
  }

  auto deserializedWrapper =
      static_cast<OperatorRegisterMoveWrapper *>(deserialized.get());
  if (deserializedWrapper->op->dst != regMove->dst ||
      deserializedWrapper->op->imm != regMove->imm) {
    cout << "FAILED (field mismatch)" << endl;
    return false;
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Stmt round trip
bool test_stmt_roundtrip() {
  cout << "Testing Stmt round trip... ";

  // Create a simple RegisterMove operator
  auto regMove = ptr<RegisterMove>();
  regMove->dst = "r2";
  regMove->imm = 100;

  auto operatorWrapper = ptr<OperatorRegisterMoveWrapper>();
  operatorWrapper->op = regMove;

  // Create a Stmt wrapping the operator
  auto stmt = ptr<StmtOperWrapper>();
  stmt->op = operatorWrapper;
  stmt->name = Option<String>("test_stmt");

  // Create a simple position
  auto pos = ptr<Pos>();
  pos->line = 10;
  pos->column = 5;
  pos->lineEnd = Option<Nat>();
  pos->columnEnd = Option<Nat>();
  pos->filename = Option<String>("test.klr");
  stmt->pos = pos;

  FILE *temp = create_temp_file();
  if (!temp) {
    cout << "FAILED (could not create temp file)" << endl;
    return false;
  }

  // Serialize
  if (!Stmt_ser(temp, stmt)) {
    cout << "FAILED (serialization failed)" << endl;
    fclose(temp);
    return false;
  }

  // Reset file position
  rewind(temp);

  // Deserialize
  Ptr<Stmt> deserialized = Stmt_des(temp);

  fclose(temp);

  // Check that we got the right type back
  if (deserialized->tag != Stmt::Tag::oper) {
    cout << "FAILED (wrong stmt tag)" << endl;
    return false;
  }

  auto deserializedStmt = static_cast<StmtOperWrapper *>(deserialized.get());

  // Check name
  if (deserializedStmt->name.has_value != stmt->name.has_value ||
      (deserializedStmt->name.has_value &&
       deserializedStmt->name.value != stmt->name.value)) {
    cout << "FAILED (name mismatch)" << endl;
    return false;
  }

  // Check position
  if (deserializedStmt->pos->line != stmt->pos->line ||
      deserializedStmt->pos->column != stmt->pos->column) {
    cout << "FAILED (position mismatch)" << endl;
    return false;
  }

  // Check operator
  if (deserializedStmt->op->tag != Operator::Tag::registerMove) {
    cout << "FAILED (wrong operator tag in stmt)" << endl;
    return false;
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Block round trip
bool test_block_roundtrip() {
  cout << "Testing Block round trip... ";

  // Create a block with a couple of statements
  auto block = ptr<Block>();
  block->label = "test_block";

  // Create first statement
  auto regMove1 = ptr<RegisterMove>();
  regMove1->dst = "r1";
  regMove1->imm = 10;
  auto op1 = ptr<OperatorRegisterMoveWrapper>();
  op1->op = regMove1;
  auto stmt1 = ptr<StmtOperWrapper>();
  stmt1->op = op1;
  stmt1->name = Option<String>();
  stmt1->pos = ptr<Pos>();
  stmt1->pos->line = 1;
  stmt1->pos->column = 1;
  stmt1->pos->lineEnd = Option<Nat>();
  stmt1->pos->columnEnd = Option<Nat>();
  stmt1->pos->filename = Option<String>();

  // Create second statement
  auto regMove2 = ptr<RegisterMove>();
  regMove2->dst = "r2";
  regMove2->imm = 20;
  auto op2 = ptr<OperatorRegisterMoveWrapper>();
  op2->op = regMove2;
  auto stmt2 = ptr<StmtOperWrapper>();
  stmt2->op = op2;
  stmt2->name = Option<String>("named_stmt");
  stmt2->pos = ptr<Pos>();
  stmt2->pos->line = 2;
  stmt2->pos->column = 1;
  stmt2->pos->lineEnd = Option<Nat>();
  stmt2->pos->columnEnd = Option<Nat>();
  stmt2->pos->filename = Option<String>();

  block->body.push_back(stmt1);
  block->body.push_back(stmt2);

  FILE *temp = create_temp_file();
  if (!temp) {
    cout << "FAILED (could not create temp file)" << endl;
    return false;
  }

  // Serialize
  if (!Block_ser(temp, block)) {
    cout << "FAILED (serialization failed)" << endl;
    fclose(temp);
    return false;
  }

  // Reset file position
  rewind(temp);

  // Deserialize
  Ptr<Block> deserialized = Block_des(temp);

  fclose(temp);

  // Check label
  if (deserialized->label != block->label) {
    cout << "FAILED (label mismatch)" << endl;
    return false;
  }

  // Check number of statements
  if (deserialized->body.size() != block->body.size()) {
    cout << "FAILED (body size mismatch)" << endl;
    return false;
  }

  // Check first statement
  auto deserStmt1 =
      static_cast<StmtOperWrapper *>(deserialized->body.front().get());
  if (deserStmt1->pos->line != 1 || deserStmt1->name.has_value) {
    cout << "FAILED (first statement mismatch)" << endl;
    return false;
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Shape round trip
bool test_shape_roundtrip() {
  cout << "Testing Shape round trip... ";

  auto shape = ptr<Shape>();
  shape->parDim = 2;
  shape->freeDims.push_back(64);
  shape->freeDims.push_back(128);
  shape->freeDims.push_back(256);

  FILE *temp = create_temp_file();
  if (!temp) {
    cout << "FAILED (could not create temp file)" << endl;
    return false;
  }

  // Serialize
  if (!Shape_ser(temp, shape)) {
    cout << "FAILED (serialization failed)" << endl;
    fclose(temp);
    return false;
  }

  // Reset file position
  rewind(temp);

  // Deserialize
  Ptr<Shape> deserialized = Shape_des(temp);

  fclose(temp);

  // Check parDim
  if (deserialized->parDim != shape->parDim) {
    cout << "FAILED (parDim mismatch)" << endl;
    return false;
  }

  // Check freeDims
  if (deserialized->freeDims.size() != shape->freeDims.size()) {
    cout << "FAILED (freeDims size mismatch)" << endl;
    return false;
  }

  auto orig_it = shape->freeDims.begin();
  auto deser_it = deserialized->freeDims.begin();
  while (orig_it != shape->freeDims.end() &&
         deser_it != deserialized->freeDims.end()) {
    if (*orig_it != *deser_it) {
      cout << "FAILED (freeDims element mismatch)" << endl;
      return false;
    }
    ++orig_it;
    ++deser_it;
  }

  cout << "PASSED" << endl;
  return true;
}

// Test ALL Operator types round trip - comprehensive coverage
bool test_all_operators_roundtrip() {
  cout << "Testing ALL Operator types round trip... ";

  int tested_count = 0;
  int passed_count = 0;

  // Helper lambda to test an operator
  auto test_operator = [&](const string &name, Ptr<Operator> op) -> bool {
    tested_count++;

    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file for " << name << ")" << endl;
      return false;
    }

    // Serialize
    if (!Operator_ser(temp, op)) {
      cout << "FAILED (serialization failed for " << name << ")" << endl;
      fclose(temp);
      return false;
    }

    // Reset file position
    rewind(temp);

    // Deserialize
    Ptr<Operator> deserialized;
    try {
      deserialized = Operator_des(temp);
    } catch (const std::exception &e) {
      cout << "FAILED (deserialization failed for " << name << ": " << e.what()
           << ")" << endl;
      fclose(temp);
      return false;
    }

    fclose(temp);

    // Check that we got the right type back
    if (deserialized->tag != op->tag) {
      cout << "FAILED (wrong operator tag for " << name << ")" << endl;
      return false;
    }

    passed_count++;
    return true;
  };

  // Helper to create a simple TensorRef (register type)
  auto create_simple_tensor_ref = [](Nat reg_num) -> Ptr<TensorRef> {
    auto tensor_ref = ptr<TensorRefRegisterWrapper>();
    tensor_ref->reg = reg_num;
    return tensor_ref;
  };

  // Helper to create a simple Immediate (int type)
  auto create_simple_immediate = [](Int value) -> Ptr<Immediate> {
    auto imm = ptr<ImmediateIntWrapper>();
    imm->i = value;
    return imm;
  };

  // Helper to create a simple Operand (immediate type)
  auto create_simple_operand = [&](Int value) -> Ptr<Operand> {
    auto operand = ptr<OperandImmWrapper>();
    operand->i = create_simple_immediate(value);
    return operand;
  };

  // Helper to create a simple DmaBounds (skip type)
  auto create_simple_dma_bounds = []() -> Ptr<DmaBounds> {
    return ptr<DmaBoundsSkipWrapper>();
  };

  // Helper to create a simple DataPattern
  auto create_simple_data_pattern = []() -> Ptr<DataPattern> {
    auto pattern = ptr<DataPattern>();
    pattern->offset = 10;
    pattern->pattern = {}; // Empty APPair list for simplicity
    pattern->channelMultiplier = 1;
    return pattern;
  };

  // Helper to create a simple IndexMissBehavior (skip type)
  auto create_simple_index_miss_behavior = []() -> Ptr<IndexMissBehavior> {
    return ptr<IndexMissBehaviorSkipWrapper>();
  };

  // Helper to create a simple TensorHbm
  auto create_simple_tensor_hbm = []() -> Ptr<TensorHbm> {
    auto tensor = ptr<TensorHbm>();
    tensor->name = "hbm_tensor";
    tensor->dtype = Dtype::float32;
    tensor->address = 0x1000;
    tensor->dims = {}; // Empty APPair list
    return tensor;
  };

  // Helper to create a simple TensorSram
  auto create_simple_tensor_sram = []() -> Ptr<TensorSram> {
    auto tensor = ptr<TensorSram>();
    tensor->name = "sram_tensor";
    tensor->dtype = Dtype::float32;
    tensor->parNum = 1;
    tensor->pattern = {}; // Empty APPair list
    tensor->parOffset = 0;
    tensor->freeOffset = 0;
    return tensor;
  };

  // Helper to create more complex TensorRef types
  auto create_hbm_tensor_ref = [&]() -> Ptr<TensorRef> {
    auto tensor_ref = ptr<TensorRefHbmWrapper>();
    tensor_ref->view = create_simple_tensor_hbm();
    return tensor_ref;
  };

  auto create_sbuf_tensor_ref = [&]() -> Ptr<TensorRef> {
    auto tensor_ref = ptr<TensorRefSbufWrapper>();
    tensor_ref->view = create_simple_tensor_sram();
    return tensor_ref;
  };

  // Helper to create a simple ReplicaGroup
  auto create_simple_replica_group = []() -> Ptr<ReplicaGroup> {
    return ptr<ReplicaGroupUnspecifiedWrapper>();
  };

  // Helper to create a simple CollectiveOp
  auto create_simple_collective_op = [&]() -> Ptr<CollectiveOp> {
    auto op = ptr<CollectiveOp>();
    op->dsts = {create_simple_tensor_ref(300)};
    op->srcs = {create_simple_tensor_ref(301)};
    op->op = Option<AluOp>(AluOp::add);
    op->replicaGroup = create_simple_replica_group();
    op->concatDim = Option<Int>();
    op->sourceTargetPairs = Option<List<List<Int>>>();
    op->channel_id = Option<Int>();
    op->num_channels = Option<Int>();
    return op;
  };

  // Test operators that don't require complex TensorRef/Immediate dependencies

  // 1. loadMaskRegister (case 16) - Simple operator
  {
    auto op = ptr<LoadMaskRegister>();
    op->regNum = 42;
    auto wrapper = ptr<OperatorLoadMaskRegisterWrapper>();
    wrapper->op = op;
    test_operator("loadMaskRegister", wrapper);
  }

  // 2. registerMove (case 45) - Simple operator with string and int
  {
    auto op = ptr<RegisterMove>();
    op->dst = "test_reg";
    op->imm = 123;
    auto wrapper = ptr<OperatorRegisterMoveWrapper>();
    wrapper->op = op;
    test_operator("registerMove", wrapper);
  }

  // 3. cmpBranch (case 46) - Operator with strings, int, and enum
  {
    auto op = ptr<CmpBranch>();
    op->reg1 = "r1";
    op->reg2 = "r2";
    op->imm = 100;
    op->op = BrCmpOp::eq_imm;
    op->trueLabel = "true_branch";
    op->falseLabel = "false_branch";
    auto wrapper = ptr<OperatorCmpBranchWrapper>();
    wrapper->op = op;
    test_operator("cmpBranch", wrapper);
  }

  // 4. registerAluOp (case 47) - Operator with strings, int, and enum
  {
    auto op = ptr<RegisterAluOp>();
    op->dst = "r_dst";
    op->src = "r_src";
    op->imm = 200;
    op->op = AluOp::add;
    auto wrapper = ptr<OperatorRegisterAluOpWrapper>();
    wrapper->op = op;
    test_operator("registerAluOp", wrapper);
  }

  // 5. rankId (case 59) - Simple operator with string
  {
    auto op = ptr<RankId>();
    op->dst = "rank_output";
    auto wrapper = ptr<OperatorRankIdWrapper>();
    wrapper->op = op;
    test_operator("rankId", wrapper);
  }

  // 6. currentProcessingRankId (case 60) - Operator with string and ints
  {
    auto op = ptr<CurrentProcessingRankId>();
    op->dst = "current_rank";
    op->iterationId = 1;
    op->channelId = 2;
    op->numChannels = 4;
    op->replicaGroup = {{1, 2}, {3, 4}};
    auto wrapper = ptr<OperatorCurrentProcessingRankIdWrapper>();
    wrapper->op = op;
    test_operator("currentProcessingRankId", wrapper);
  }

  // 7. extendedInst (case 69) - Operator with basic fields
  {
    auto op = ptr<ExtendedInst>();
    op->opcode = 42;
    op->hasRead = true;
    op->hasWrite = false;
    op->ports = 2;
    op->data0 = {1, 2, 3};
    op->data1 = {4, 5, 6};
    auto wrapper = ptr<OperatorExtendedInstWrapper>();
    wrapper->op = op;
    test_operator("extendedInst", wrapper);
  }

  // Now test operators that use simple TensorRef (register type)

  // 8. tensorLoad (case 43) - Uses TensorRef
  {
    auto op = ptr<TensorLoad>();
    op->dst = "tensor_dst";
    op->src = create_simple_tensor_ref(10);
    auto wrapper = ptr<OperatorTensorLoadWrapper>();
    wrapper->op = op;
    test_operator("tensorLoad", wrapper);
  }

  // 9. tensorStore (case 44) - Uses TensorRef
  {
    auto op = ptr<TensorStore>();
    op->dst = create_simple_tensor_ref(20);
    op->src = "tensor_src";
    auto wrapper = ptr<OperatorTensorStoreWrapper>();
    wrapper->op = op;
    test_operator("tensorStore", wrapper);
  }

  // 10. memSet (case 25) - Uses TensorRef and Immediate
  {
    auto op = ptr<MemSet>();
    op->dst = create_simple_tensor_ref(30);
    op->value = create_simple_immediate(42);
    op->dtype = Dtype::float32;
    op->engine = Engine::dma;
    auto wrapper = ptr<OperatorMemSetWrapper>();
    wrapper->op = op;
    test_operator("memSet", wrapper);
  }

  // 11. copy (case 7) - Uses TensorRef
  {
    auto op = ptr<Copy>();
    op->dst = create_simple_tensor_ref(40);
    op->src = create_simple_tensor_ref(41);
    op->opDim = Option<TensorSubDim>();
    auto wrapper = ptr<OperatorCopyWrapper>();
    wrapper->op = op;
    test_operator("copy", wrapper);
  }

  // 12. ncCopy (case 8) - Uses TensorRef
  {
    auto op = ptr<NcCopy>();
    op->dst = create_simple_tensor_ref(50);
    op->src = create_simple_tensor_ref(51);
    op->dtype = Option<Dtype>();
    op->engine = Engine::dma;
    auto wrapper = ptr<OperatorNcCopyWrapper>();
    wrapper->op = op;
    test_operator("ncCopy", wrapper);
  }

  // 13. tensorTensor (case 34) - Uses TensorRef
  {
    auto op = ptr<TensorTensor>();
    op->dst = create_simple_tensor_ref(60);
    op->src0 = create_simple_tensor_ref(61);
    op->src1 = create_simple_tensor_ref(62);
    op->op = AluOp::add;
    op->dtype = Option<Dtype>();
    op->engine = Engine::pe;
    auto wrapper = ptr<OperatorTensorTensorWrapper>();
    wrapper->op = op;
    test_operator("tensorTensor", wrapper);
  }

  // 14. tensorReduce (case 32) - Uses TensorRef
  {
    auto op = ptr<TensorReduce>();
    op->dst = create_simple_tensor_ref(70);
    op->src = create_simple_tensor_ref(71);
    op->op = AluOp::add;
    op->opDim = TensorSubDim::X;
    op->negated = false;
    op->dtype = Option<Dtype>();
    op->keepdims = true;
    auto wrapper = ptr<OperatorTensorReduceWrapper>();
    wrapper->op = op;
    test_operator("tensorReduce", wrapper);
  }

  // 15. transpose (case 38) - Uses TensorRef
  {
    auto op = ptr<Transpose>();
    op->dst = create_simple_tensor_ref(80);
    op->src = create_simple_tensor_ref(81);
    op->dtype = Option<Dtype>();
    op->engine = Engine::dma;
    auto wrapper = ptr<OperatorTransposeWrapper>();
    wrapper->op = op;
    test_operator("transpose", wrapper);
  }

  // 16. dmaCopy (case 10) - Uses TensorRef and DmaBounds
  {
    auto op = ptr<DmaCopy>();
    op->dst = create_simple_tensor_ref(90);
    op->src = create_simple_tensor_ref(91);
    op->compute_op = DgeComputeOp::none;
    op->dstBoundsCheck = create_simple_dma_bounds();
    op->srcBoundsCheck = create_simple_dma_bounds();
    auto wrapper = ptr<OperatorDmaCopyWrapper>();
    wrapper->op = op;
    test_operator("dmaCopy", wrapper);
  }

  // 17. ncDmaCopy (case 11) - Uses TensorRef and DmaBounds
  {
    auto op = ptr<NcDmaCopy>();
    op->dst = create_simple_tensor_ref(100);
    op->src = create_simple_tensor_ref(101);
    op->compute_op = DgeComputeOp::none;
    op->oobMode = create_simple_dma_bounds();
    op->dgeMode = 0;
    op->uniqueIndices = false;
    op->engine = Engine::dma;
    auto wrapper = ptr<OperatorNcDmaCopyWrapper>();
    wrapper->op = op;
    test_operator("ncDmaCopy", wrapper);
  }

  // 18. dmaTranspose (case 12) - Uses TensorRef and DmaBounds
  {
    auto op = ptr<DmaTranspose>();
    op->dst = create_simple_tensor_ref(110);
    op->src = create_simple_tensor_ref(111);
    op->axes = TransposeOps::None;
    op->dtype = Option<Dtype>();
    op->dgeMode = 0;
    op->oobMode = create_simple_dma_bounds();
    auto wrapper = ptr<OperatorDmaTransposeWrapper>();
    wrapper->op = op;
    test_operator("dmaTranspose", wrapper);
  }

  // 19. tensorScalar (case 33) - Uses TensorRef and Operand
  {
    auto op = ptr<TensorScalar>();
    op->dst = create_simple_tensor_ref(120);
    op->src = create_simple_tensor_ref(121);
    op->imm0 = create_simple_operand(42);
    op->op0 = AluOp::add;
    op->imm1 = Option<Ptr<Operand>>();
    op->op1 = Option<AluOp>();
    op->reverse = TensorScalarReverseOps::none;
    op->engine = Engine::pe;
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorTensorScalarWrapper>();
    wrapper->op = op;
    test_operator("tensorScalar", wrapper);
  }

  // 20. rng (case 64) - Uses TensorRef
  {
    auto op = ptr<Rng>();
    op->dst = create_simple_tensor_ref(130);
    op->engine = Engine::pe;
    auto wrapper = ptr<OperatorRngWrapper>();
    wrapper->op = op;
    test_operator("rng", wrapper);
  }

  // 21. randGetState (case 66) - Uses TensorRef
  {
    auto op = ptr<RandGetState>();
    op->dst = create_simple_tensor_ref(140);
    op->engine = Engine::act;
    auto wrapper = ptr<OperatorRandGetStateWrapper>();
    wrapper->op = op;
    test_operator("randGetState", wrapper);
  }

  // 22. setRngSeed (case 67) - Uses TensorRef
  {
    auto op = ptr<SetRngSeed>();
    op->src = create_simple_tensor_ref(150);
    auto wrapper = ptr<OperatorSetRngSeedWrapper>();
    wrapper->op = op;
    test_operator("setRngSeed", wrapper);
  }

  // 23. randSetState (case 68) - Uses TensorRef
  {
    auto op = ptr<RandSetState>();
    op->src = create_simple_tensor_ref(160);
    op->engine = Engine::dve;
    auto wrapper = ptr<OperatorRandSetStateWrapper>();
    wrapper->op = op;
    test_operator("randSetState", wrapper);
  }

  // 24. loadStationary (case 17) - Uses TensorRef
  {
    auto op = ptr<LoadStationary>();
    op->src = create_simple_tensor_ref(170);
    op->isTranspose = true;
    auto wrapper = ptr<OperatorLoadStationaryWrapper>();
    wrapper->op = op;
    test_operator("loadStationary", wrapper);
  }

  // 25. matMul (case 20) - Uses TensorRef
  {
    auto op = ptr<MatMul>();
    op->dst = create_simple_tensor_ref(180);
    op->moving = create_simple_tensor_ref(181);
    auto wrapper = ptr<OperatorMatMulWrapper>();
    wrapper->op = op;
    test_operator("matMul", wrapper);
  }

  // 26. matchValueLoad (case 23) - Uses TensorRef
  {
    auto op = ptr<MatchValueLoad>();
    op->src = create_simple_tensor_ref(190);
    auto wrapper = ptr<OperatorMatchValueLoadWrapper>();
    wrapper->op = op;
    test_operator("matchValueLoad", wrapper);
  }

  // 27. max8 (case 24) - Uses TensorRef
  {
    auto op = ptr<Max8>();
    op->dst = create_simple_tensor_ref(200);
    op->src = create_simple_tensor_ref(201);
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorMax8Wrapper>();
    wrapper->op = op;
    test_operator("max8", wrapper);
  }

  // 28. batchNormAggregate (case 5) - Uses TensorRef
  {
    auto op = ptr<BatchNormAggregate>();
    op->dst = create_simple_tensor_ref(210);
    op->src = create_simple_tensor_ref(211);
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorBatchNormAggregateWrapper>();
    wrapper->op = op;
    test_operator("batchNormAggregate", wrapper);
  }

  // 29. batchNormStats (case 6) - Uses TensorRef
  {
    auto op = ptr<BatchNormStats>();
    op->dst = create_simple_tensor_ref(220);
    op->src = create_simple_tensor_ref(221);
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorBatchNormStatsWrapper>();
    wrapper->op = op;
    test_operator("batchNormStats", wrapper);
  }

  // 30. reciprocal (case 28) - Uses TensorRef
  {
    auto op = ptr<Reciprocal>();
    op->dst = create_simple_tensor_ref(230);
    op->src = create_simple_tensor_ref(231);
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorReciprocalWrapper>();
    wrapper->op = op;
    test_operator("reciprocal", wrapper);
  }

  // 31. sequenceBounds (case 40) - Uses TensorRef
  {
    auto op = ptr<SequenceBounds>();
    op->dst = create_simple_tensor_ref(240);
    op->segmentIds = create_simple_tensor_ref(241);
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorSequenceBoundsWrapper>();
    wrapper->op = op;
    test_operator("sequenceBounds", wrapper);
  }

  // 32. quantizeMX (case 48) - Uses TensorRef
  {
    auto op = ptr<QuantizeMX>();
    op->dst = create_simple_tensor_ref(250);
    op->src = create_simple_tensor_ref(251);
    op->dstScale = create_simple_tensor_ref(252);
    auto wrapper = ptr<OperatorQuantizeMXWrapper>();
    wrapper->op = op;
    test_operator("quantizeMX", wrapper);
  }

  // 33. tensorPartitionReduce (case 36) - Uses TensorRef
  {
    auto op = ptr<TensorPartitionReduce>();
    op->dst = create_simple_tensor_ref(260);
    op->op = AluOp::add;
    op->data = create_simple_tensor_ref(261);
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorTensorPartitionReduceWrapper>();
    wrapper->op = op;
    test_operator("tensorPartitionReduce", wrapper);
  }

  // 34. rand2 (case 65) - Uses TensorRef and Operand
  {
    auto op = ptr<Rand2>();
    op->dst = create_simple_tensor_ref(270);
    op->min = create_simple_operand(0);
    op->max = create_simple_operand(100);
    auto wrapper = ptr<OperatorRand2Wrapper>();
    wrapper->op = op;
    test_operator("rand2", wrapper);
  }

  // 35. copyPredicated (case 9) - Uses TensorRef
  {
    auto op = ptr<CopyPredicated>();
    op->dst = create_simple_tensor_ref(280);
    op->src = create_simple_tensor_ref(281);
    op->predicate = create_simple_tensor_ref(282);
    op->dtype = Option<Dtype>();
    op->reversePred = false;
    auto wrapper = ptr<OperatorCopyPredicatedWrapper>();
    wrapper->op = op;
    test_operator("copyPredicated", wrapper);
  }

  // 36. findIndex8 (case 14) - Uses TensorRef
  {
    auto op = ptr<FindIndex8>();
    op->dst = create_simple_tensor_ref(290);
    op->src = create_simple_tensor_ref(291);
    op->vals = create_simple_tensor_ref(292);
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorFindIndex8Wrapper>();
    wrapper->op = op;
    test_operator("findIndex8", wrapper);
  }

  // 37. iota (case 15) - Uses TensorRef and DataPattern
  {
    auto op = ptr<Iota>();
    op->dst = create_simple_tensor_ref(300);
    op->pattern = create_simple_data_pattern();
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorIotaWrapper>();
    wrapper->op = op;
    test_operator("iota", wrapper);
  }

  // 38. localGather (case 18) - Uses TensorRef and IndexMissBehavior
  {
    auto op = ptr<LocalGather>();
    op->dst = create_simple_tensor_ref(310);
    op->src = create_simple_tensor_ref(311);
    op->indexMissBehavior = create_simple_index_miss_behavior();
    op->freePoolBuffer = true;
    auto wrapper = ptr<OperatorLocalGatherWrapper>();
    wrapper->op = op;
    test_operator("localGather", wrapper);
  }

  // 39. ncMatMul (case 21) - Uses TensorRef and lists
  {
    auto op = ptr<NcMatMul>();
    op->dst = create_simple_tensor_ref(320);
    op->stationary = create_simple_tensor_ref(321);
    op->moving = create_simple_tensor_ref(322);
    op->isStationaryOneZero = false;
    op->isMovingZero = false;
    op->isTranspose = true;
    op->tilePosition = {1, 2};
    op->tileSize = {64, 64};
    op->perfMode = MatmulPerfMode::None;
    auto wrapper = ptr<OperatorNcMatMulWrapper>();
    wrapper->op = op;
    test_operator("ncMatMul", wrapper);
  }

  // 40. shuffle (case 31) - Uses TensorRef and List<Immediate>
  {
    auto op = ptr<Shuffle>();
    op->dst = create_simple_tensor_ref(330);
    op->src = create_simple_tensor_ref(331);
    op->shuffleMask = {create_simple_immediate(0), create_simple_immediate(1)};
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorShuffleWrapper>();
    wrapper->op = op;
    test_operator("shuffle", wrapper);
  }

  // 41. tensorTensorScan (case 35) - Uses TensorRef and Operand
  {
    auto op = ptr<TensorTensorScan>();
    op->dst = create_simple_tensor_ref(340);
    op->src0 = create_simple_tensor_ref(341);
    op->src1 = create_simple_tensor_ref(342);
    op->op0 = AluOp::add;
    op->op1 = AluOp::mult;
    op->reverseOperands = TensorScalarReverseOps::none;
    op->imm0 = create_simple_operand(42);
    op->accumulatorCmd = AccumCmd::Accumulate;
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorTensorTensorScanWrapper>();
    wrapper->op = op;
    test_operator("tensorTensorScan", wrapper);
  }

  // 42. tensorScalarReduce (case 37) - Uses TensorRef and Operand
  {
    auto op = ptr<TensorScalarReduce>();
    op->dst = create_simple_tensor_ref(350);
    op->src = create_simple_tensor_ref(351);
    op->operand0 = create_simple_operand(10);
    op->op0 = AluOp::add;
    op->reverse0 = false;
    op->dtype = Option<Dtype>();
    op->reduceOp = Option<AluOp>();
    op->reduceRes = create_simple_tensor_ref(352);
    auto wrapper = ptr<OperatorTensorScalarReduceWrapper>();
    wrapper->op = op;
    test_operator("tensorScalarReduce", wrapper);
  }

  // 43. selectReduce (case 39) - Uses TensorRef and Operand
  {
    auto op = ptr<SelectReduce>();
    op->dst = create_simple_tensor_ref(360);
    op->predicate = create_simple_tensor_ref(361);
    op->onTrue = create_simple_tensor_ref(362);
    op->onFalse = create_simple_operand(0);
    op->reduceRes = Option<Ptr<TensorRef>>();
    op->reduceCmd = AccumCmd::Zero;
    op->reduceOp = AluOp::add;
    op->reversePred = false;
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorSelectReduceWrapper>();
    wrapper->op = op;
    test_operator("selectReduce", wrapper);
  }

  // 44. sendRecv (case 41) - Uses TensorRef and Immediate
  {
    auto op = ptr<SendRecv>();
    op->dst = create_simple_tensor_ref(370);
    op->src = create_simple_tensor_ref(371);
    op->sendToRank = create_simple_immediate(1);
    op->recvFromRank = create_simple_immediate(2);
    op->pipeId = create_simple_immediate(0);
    op->useGpsimdDma = false;
    auto wrapper = ptr<OperatorSendRecvWrapper>();
    wrapper->op = op;
    test_operator("sendRecv", wrapper);
  }

  // 45. sendRecvCompute (case 42) - Uses Lists of TensorRef and Immediate
  {
    auto op = ptr<SendRecvCompute>();
    op->dsts = {create_simple_tensor_ref(380)};
    op->srcs = {create_simple_tensor_ref(381)};
    op->sendToRanks = {create_simple_immediate(1)};
    op->recvFromRanks = {create_simple_immediate(2)};
    op->pipeId = create_simple_immediate(0);
    op->op = AluOp::add;
    auto wrapper = ptr<OperatorSendRecvComputeWrapper>();
    wrapper->op = op;
    test_operator("sendRecvCompute", wrapper);
  }

  // 46. dmaCompute (case 50) - Uses Lists of TensorRef and Immediate
  {
    auto op = ptr<DmaCompute>();
    op->dst = create_simple_tensor_ref(390);
    op->srcs = {create_simple_tensor_ref(391)};
    op->scales = {create_simple_immediate(1)};
    op->reduceOp = AluOp::add;
    auto wrapper = ptr<OperatorDmaComputeWrapper>();
    wrapper->op = op;
    test_operator("dmaCompute", wrapper);
  }

  // 47. allReduce (case 51) - Uses CollectiveOp
  {
    auto wrapper = ptr<OperatorAllReduceWrapper>();
    wrapper->op = create_simple_collective_op();
    test_operator("allReduce", wrapper);
  }

  // 48. allGather (case 52) - Uses CollectiveOp
  {
    auto wrapper = ptr<OperatorAllGatherWrapper>();
    wrapper->op = create_simple_collective_op();
    test_operator("allGather", wrapper);
  }

  // 49. reduceScatter (case 53) - Uses CollectiveOp
  {
    auto wrapper = ptr<OperatorReduceScatterWrapper>();
    wrapper->op = create_simple_collective_op();
    test_operator("reduceScatter", wrapper);
  }

  // 50. collectivePermute (case 54) - Uses CollectiveOp
  {
    auto wrapper = ptr<OperatorCollectivePermuteWrapper>();
    wrapper->op = create_simple_collective_op();
    test_operator("collectivePermute", wrapper);
  }

  // 51. send (case 61) - Uses TensorRef list
  {
    auto op = ptr<Send>();
    op->op = AluOp::add;
    op->srcs = {create_simple_tensor_ref(400)};
    op->peerId = 1;
    auto wrapper = ptr<OperatorSendWrapper>();
    wrapper->op = op;
    test_operator("send", wrapper);
  }

  // 52. recv (case 62) - Uses TensorRef list
  {
    auto op = ptr<Recv>();
    op->op = AluOp::add;
    op->dsts = {create_simple_tensor_ref(410)};
    op->replicaGroups = {1, 2};
    op->peerId = 1;
    auto wrapper = ptr<OperatorRecvWrapper>();
    wrapper->op = op;
    test_operator("recv", wrapper);
  }

  // 53. coreBarrier (case 63) - Uses TensorRef and Int list
  {
    auto op = ptr<CoreBarrier>();
    op->data = create_simple_tensor_ref(420);
    op->cores = {0, 1, 2};
    op->engine = Engine::dma;
    auto wrapper = ptr<OperatorCoreBarrierWrapper>();
    wrapper->op = op;
    test_operator("coreBarrier", wrapper);
  }

  // 54. tensorScalarCumulative (case 70) - Uses TensorRef and Operand
  {
    auto op = ptr<TensorScalarCumulative>();
    op->dst = create_simple_tensor_ref(430);
    op->src = create_simple_tensor_ref(431);
    op->op0 = AluOp::add;
    op->op1 = AluOp::mult;
    op->imm0 = create_simple_operand(1);
    op->imm1 = Option<Ptr<Operand>>();
    op->reduceCmd = AccumCmd::Accumulate;
    op->reverse = TensorScalarReverseOps::none;
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorTensorScalarCumulativeWrapper>();
    wrapper->op = op;
    test_operator("tensorScalarCumulative", wrapper);
  }

  // 55. ncNGather (case 71) - Uses TensorRef
  {
    auto op = ptr<NcNGather>();
    op->dst = create_simple_tensor_ref(440);
    op->data = create_simple_tensor_ref(441);
    op->indices = create_simple_tensor_ref(442);
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorNcNGatherWrapper>();
    wrapper->op = op;
    test_operator("ncNGather", wrapper);
  }

  // 56. devicePrint (case 72) - Uses TensorRef
  {
    auto op = ptr<DevicePrint>();
    op->src = create_simple_tensor_ref(450);
    op->printPrefix = "DEBUG: ";
    op->buffer = PrintOutputBuffer::stdout;
    auto wrapper = ptr<OperatorDevicePrintWrapper>();
    wrapper->op = op;
    test_operator("devicePrint", wrapper);
  }

  // Now test the remaining complex operators that require more sophisticated
  // implementations

  // 57. rangeSelect (case 26) - Uses TensorRef and Immediate
  {
    auto op = ptr<RangeSelect>();
    op->dst = create_simple_tensor_ref(460);
    op->src = create_simple_tensor_ref(461);
    op->reduceCommand = AccumCmd::Accumulate;
    op->reduceOp = AluOp::add;
    op->base = 0.0f;
    op->fillValue = 1.0f;
    op->compOp0 = AluOp::is_ge;
    op->compOp1 = AluOp::is_le;
    op->bound0 = create_simple_immediate(0);
    op->bound1 = create_simple_immediate(100);
    auto wrapper = ptr<OperatorRangeSelectWrapper>();
    wrapper->op = op;
    test_operator("rangeSelect", wrapper);
  }

  // 58. scalarTensorTensor (case 29) - Uses TensorRef and Immediate
  {
    auto op = ptr<ScalarTensorTensor>();
    op->dst = create_simple_tensor_ref(470);
    op->src0 = create_simple_tensor_ref(471);
    op->src1 = create_simple_tensor_ref(472);
    op->op0 = AluOp::add;
    op->op1 = AluOp::mult;
    op->reverseOperands = TensorScalarReverseOps::none;
    op->imm0 = create_simple_immediate(1);
    op->accumulatorCmd = AccumCmd::Accumulate;
    auto wrapper = ptr<OperatorScalarTensorTensorWrapper>();
    wrapper->op = op;
    test_operator("scalarTensorTensor", wrapper);
  }

  // 59. matchReplace8 (case 22) - Uses TensorRef and Immediate
  {
    auto op = ptr<MatchReplace8>();
    op->dst = create_simple_tensor_ref(480);
    op->src = create_simple_tensor_ref(481);
    op->vals = create_simple_tensor_ref(482);
    op->replaceValue = create_simple_immediate(42);
    op->dstIdx = Option<Ptr<TensorRef>>();
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorMatchReplace8Wrapper>();
    wrapper->op = op;
    test_operator("matchReplace8", wrapper);
  }

  // 60. ncMatMulMX (case 49) - Uses TensorRef and optional lists
  {
    auto op = ptr<MatMulMX>();
    op->dst = create_simple_tensor_ref(490);
    op->stationary = create_simple_tensor_ref(491);
    op->moving = create_simple_tensor_ref(492);
    op->stationaryScale = create_simple_tensor_ref(493);
    op->movingScale = create_simple_tensor_ref(494);
    op->tilePosition = Option<List<Nat>>();
    op->tileSize = Option<List<Nat>>();
    auto wrapper = ptr<OperatorNcMatMulMXWrapper>();
    wrapper->op = op;
    test_operator("ncMatMulMX", wrapper);
  }

  // 61. collectivePermuteImplicit (case 55) - Uses CollectiveOp
  {
    auto wrapper = ptr<OperatorCollectivePermuteImplicitWrapper>();
    wrapper->op = create_simple_collective_op();
    test_operator("collectivePermuteImplicit", wrapper);
  }

  // 62. collectivePermuteImplicitReduce (case 56) - Uses CollectiveOp
  {
    auto wrapper = ptr<OperatorCollectivePermuteImplicitReduceWrapper>();
    wrapper->op = create_simple_collective_op();
    test_operator("collectivePermuteImplicitReduce", wrapper);
  }

  // 63. broadcast (case 57) - Uses CollectiveOp
  {
    auto wrapper = ptr<OperatorBroadcastWrapper>();
    wrapper->op = create_simple_collective_op();
    test_operator("broadcast", wrapper);
  }

  // 64. allToAll (case 58) - Uses CollectiveOp
  {
    auto wrapper = ptr<OperatorAllToAllWrapper>();
    wrapper->op = create_simple_collective_op();
    test_operator("allToAll", wrapper);
  }

  // The remaining 9 operators require complex Access patterns or other advanced
  // types Let's implement them with simplified versions where possible

  // 65. dropout (case 13) - Uses TensorRef and Operand
  {
    auto op = ptr<Dropout>();
    op->dst = create_simple_tensor_ref(500);
    op->src = create_simple_tensor_ref(501);
    op->thresholdType = DropoutThresholdType::DropRate;
    op->threshold = create_simple_operand(50); // 50% dropout rate
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorDropoutWrapper>();
    wrapper->op = op;
    test_operator("dropout", wrapper);
  }

  // 66. activate (case 0) - Uses TensorRef and Immediate
  {
    auto op = ptr<Activate>();
    op->dst = create_simple_tensor_ref(510);
    op->src = create_simple_tensor_ref(511);
    op->accumulatorCmd = AccumCmd::Accumulate;
    op->activationFunc = ActivationFunc::relu;
    op->scale = create_simple_immediate(1);
    op->bias = create_simple_immediate(0);
    op->imm = create_simple_immediate(0);
    auto wrapper = ptr<OperatorActivateWrapper>();
    wrapper->op = op;
    test_operator("activate", wrapper);
  }

  // 67. ncActivate (case 1) - Uses TensorRef and Operand
  {
    auto op = ptr<NcActivate>();
    op->dst = create_simple_tensor_ref(520);
    op->src = create_simple_tensor_ref(521);
    op->accumulatorCmd = AccumCmd::Accumulate;
    op->activationFunc = ActivationFunc::sigmoid;
    op->scale = create_simple_operand(1);
    op->bias = Option<Ptr<TensorRef>>();
    op->reduceOp = Option<AluOp>();
    op->reduceRes = Option<Ptr<TensorRef>>();
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorNcActivateWrapper>();
    wrapper->op = op;
    test_operator("ncActivate", wrapper);
  }

  // 68. activationReduce (case 2) - Uses NcActivate (same as ncActivate)
  {
    auto op = ptr<NcActivate>();
    op->dst = create_simple_tensor_ref(530);
    op->src = create_simple_tensor_ref(531);
    op->accumulatorCmd = AccumCmd::Zero;
    op->activationFunc = ActivationFunc::tanh;
    op->scale = create_simple_operand(1);
    op->bias = Option<Ptr<TensorRef>>();
    op->reduceOp = Option<AluOp>(AluOp::add);
    op->reduceRes = Option<Ptr<TensorRef>>(create_simple_tensor_ref(532));
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorActivationReduceWrapper>();
    wrapper->op = op;
    test_operator("activationReduce", wrapper);
  }

  // 69. affineSelect (case 3) - Uses TensorRef and DataPattern
  {
    auto op = ptr<AffineSelect>();
    op->dst = create_simple_tensor_ref(540);
    op->src = create_simple_tensor_ref(541);
    op->fillMode = AffineSelectCmp::GreaterThan;
    op->fillReg = 42;
    op->maskPattern = create_simple_data_pattern();
    auto wrapper = ptr<OperatorAffineSelectWrapper>();
    wrapper->op = op;
    test_operator("affineSelect", wrapper);
  }

  // 70. ncAffineSelect (case 4) - Uses TensorRef, DataPattern, and Immediate
  {
    auto op = ptr<NcAffineSelect>();
    op->dst = create_simple_tensor_ref(550);
    op->pred = create_simple_data_pattern();
    op->onTrueTile = create_simple_tensor_ref(551);
    op->onFalseValue = create_simple_immediate(0);
    op->dtype = Option<Dtype>();
    op->cmpOp = AluOp::is_gt;
    auto wrapper = ptr<OperatorNcAffineSelectWrapper>();
    wrapper->op = op;
    test_operator("ncAffineSelect", wrapper);
  }

  // 71. ncLocalGather (case 19) - Uses TensorRef and Immediate
  {
    auto op = ptr<NcLocalGather>();
    op->dst = create_simple_tensor_ref(560);
    op->src = create_simple_tensor_ref(561);
    op->index = create_simple_tensor_ref(562);
    op->numElemPerIdx = create_simple_immediate(4);
    op->numValidIndicies = Option<Ptr<Immediate>>();
    auto wrapper = ptr<OperatorNcLocalGatherWrapper>();
    wrapper->op = op;
    test_operator("ncLocalGather", wrapper);
  }

  // 72. ncRangeSelect (case 27) - Uses TensorRef and Immediate
  {
    auto op = ptr<NcRangeSelect>();
    op->dst = create_simple_tensor_ref(570);
    op->reduceCommand = AccumCmd::Accumulate;
    op->reduceRes = Option<Ptr<TensorRef>>();
    op->reduceOp = Option<AluOp>();
    op->compOp0 = AluOp::is_ge;
    op->compOp1 = AluOp::is_le;
    op->bound0 = create_simple_tensor_ref(571);
    op->bound1 = create_simple_tensor_ref(572);
    op->rangeStart = create_simple_immediate(0);
    op->onTrueTile = create_simple_tensor_ref(573);
    op->onFalseValue = create_simple_immediate(0);
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorNcRangeSelectWrapper>();
    wrapper->op = op;
    test_operator("ncRangeSelect", wrapper);
  }

  // 73. ncScalarTensorTensor (case 30) - Uses TensorRef and Operand
  {
    auto op = ptr<NcScalarTensorTensor>();
    op->dst = create_simple_tensor_ref(580);
    op->data = create_simple_tensor_ref(581);
    op->src0 = create_simple_operand(1);
    op->src1 = create_simple_operand(2);
    op->op0 = AluOp::add;
    op->op1 = AluOp::mult;
    op->reverseOperands = TensorScalarReverseOps::none;
    op->dtype = Option<Dtype>();
    auto wrapper = ptr<OperatorNcScalarTensorTensorWrapper>();
    wrapper->op = op;
    test_operator("ncScalarTensorTensor", wrapper);
  }

  cout << "PASSED (" << passed_count << "/" << tested_count
       << " operators tested, " << (73 - tested_count)
       << " skipped due to complex dependencies)" << endl;

  return passed_count == tested_count; // All tested operators must pass
}

// Test TensorName round trip (complex struct with nested types)
bool test_tensor_name_roundtrip() {
  cout << "Testing TensorName round trip... ";

  auto tensorName = ptr<TensorName>();
  tensorName->name = "test_tensor";
  tensorName->dtype = Dtype::float32;
  tensorName->freeElements = 4096;
  tensorName->addressRotation = false;

  // Create shape
  auto shape = ptr<Shape>();
  shape->parDim = 1;
  shape->freeDims.push_back(64);
  shape->freeDims.push_back(64);
  tensorName->shape = shape;

  // Create address
  auto address = ptr<Address>();
  address->name = "tensor_addr";
  address->memory = Memory::sbuf;
  address->parSize = 1;
  address->freeSize = 4096;
  address->parOffset = Option<Nat>(0);
  address->freeOffset = Option<Nat>(1024);
  address->isShared = false;
  tensorName->address = address;

  // Set WF props (empty for now)
  tensorName->parWF = Prop{};
  tensorName->freeWF = Prop{};

  FILE *temp = create_temp_file();
  if (!temp) {
    cout << "FAILED (could not create temp file)" << endl;
    return false;
  }

  // Serialize
  if (!TensorName_ser(temp, tensorName)) {
    cout << "FAILED (serialization failed)" << endl;
    fclose(temp);
    return false;
  }

  // Reset file position
  rewind(temp);

  // Deserialize
  Ptr<TensorName> deserialized = TensorName_des(temp);

  fclose(temp);

  // Check basic fields
  if (deserialized->name != tensorName->name ||
      deserialized->dtype != tensorName->dtype ||
      deserialized->freeElements != tensorName->freeElements ||
      deserialized->addressRotation != tensorName->addressRotation) {
    cout << "FAILED (basic field mismatch)" << endl;
    return false;
  }

  // Check shape
  if (deserialized->shape->parDim != tensorName->shape->parDim ||
      deserialized->shape->freeDims.size() !=
          tensorName->shape->freeDims.size()) {
    cout << "FAILED (shape mismatch)" << endl;
    return false;
  }

  // Check address
  if (deserialized->address->name != tensorName->address->name ||
      deserialized->address->memory != tensorName->address->memory ||
      deserialized->address->parSize != tensorName->address->parSize ||
      deserialized->address->freeSize != tensorName->address->freeSize ||
      deserialized->address->isShared != tensorName->address->isShared) {
    cout << "FAILED (address mismatch)" << endl;
    return false;
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Address round trip
bool test_address_roundtrip() {
  cout << "Testing Address round trip... ";

  auto address = ptr<Address>();
  address->name = "test_address";
  address->memory = Memory::hbm;
  address->parSize = 1024;
  address->freeSize = 2048;
  address->parOffset = Option<Nat>(100);
  address->freeOffset = Option<Nat>();
  address->isShared = true;

  FILE *temp = create_temp_file();
  if (!temp) {
    cout << "FAILED (could not create temp file)" << endl;
    return false;
  }

  // Serialize
  if (!Address_ser(temp, address)) {
    cout << "FAILED (serialization failed)" << endl;
    fclose(temp);
    return false;
  }

  // Reset file position
  rewind(temp);

  // Deserialize
  Ptr<Address> deserialized = Address_des(temp);

  fclose(temp);

  // Check all fields
  if (deserialized->name != address->name ||
      deserialized->memory != address->memory ||
      deserialized->parSize != address->parSize ||
      deserialized->freeSize != address->freeSize ||
      deserialized->isShared != address->isShared) {
    cout << "FAILED (basic field mismatch)" << endl;
    return false;
  }

  // Check optional fields
  if (deserialized->parOffset.has_value != address->parOffset.has_value ||
      deserialized->freeOffset.has_value != address->freeOffset.has_value) {
    cout << "FAILED (optional field presence mismatch)" << endl;
    return false;
  }

  if (address->parOffset.has_value &&
      deserialized->parOffset.value != address->parOffset.value) {
    cout << "FAILED (parOffset value mismatch)" << endl;
    return false;
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Dtype enum round trip
bool test_dtype_roundtrip() {
  cout << "Testing Dtype enum round trip... ";

  vector<Dtype> test_values = {Dtype::bfloat16, Dtype::float8e3,
                               Dtype::float32,  Dtype::int8,
                               Dtype::uint32,   Dtype::float8_e4m3fn_x4};

  for (const Dtype &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!Dtype_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    Dtype deserialized = Dtype_des(temp);
    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Engine enum round trip
bool test_engine_roundtrip() {
  cout << "Testing Engine enum round trip... ";

  vector<Engine> test_values = {Engine::unassigned, Engine::act, Engine::dma,
                                Engine::pe, Engine::pool};

  for (const Engine &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!Engine_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    Engine deserialized = Engine_des(temp);
    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test AluOp enum round trip
bool test_aluop_roundtrip() {
  cout << "Testing AluOp enum round trip... ";

  vector<AluOp> test_values = {AluOp::abs, AluOp::add, AluOp::mult, AluOp::max,
                               AluOp::subtract};

  for (const AluOp &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!AluOp_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    AluOp deserialized = AluOp_des(temp);
    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Immediate sum type round trip
bool test_immediate_roundtrip() {
  cout << "Testing Immediate sum type round trip... ";

  // Test register variant
  {
    auto imm = ptr<ImmediateRegisterWrapper>();
    imm->reg = 42;

    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!Immediate_ser(temp, imm)) {
      cout << "FAILED (register serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    Ptr<Immediate> deserialized = Immediate_des(temp);
    fclose(temp);

    if (deserialized->tag != Immediate::Tag::reg) {
      cout << "FAILED (wrong tag for register)" << endl;
      return false;
    }

    auto typed = static_cast<ImmediateRegisterWrapper *>(deserialized.get());
    if (typed->reg != 42) {
      cout << "FAILED (register value mismatch)" << endl;
      return false;
    }
  }

  // Test int variant
  {
    auto imm = ptr<ImmediateIntWrapper>();
    imm->i = -123;

    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!Immediate_ser(temp, imm)) {
      cout << "FAILED (int serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    Ptr<Immediate> deserialized = Immediate_des(temp);
    fclose(temp);

    if (deserialized->tag != Immediate::Tag::int32) {
      cout << "FAILED (wrong tag for int)" << endl;
      return false;
    }

    auto typed = static_cast<ImmediateIntWrapper *>(deserialized.get());
    if (typed->i != -123) {
      cout << "FAILED (int value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test TensorRef sum type round trip
bool test_tensorref_roundtrip() {
  cout << "Testing TensorRef sum type round trip... ";

  // Test register variant
  {
    auto tensorRef = ptr<TensorRefRegisterWrapper>();
    tensorRef->reg = 99;

    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!TensorRef_ser(temp, tensorRef)) {
      cout << "FAILED (register serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    Ptr<TensorRef> deserialized = TensorRef_des(temp);
    fclose(temp);

    if (deserialized->tag != TensorRef::Tag::reg) {
      cout << "FAILED (wrong tag for register)" << endl;
      return false;
    }

    auto typed = static_cast<TensorRefRegisterWrapper *>(deserialized.get());
    if (typed->reg != 99) {
      cout << "FAILED (register value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Slice struct round trip
bool test_slice_roundtrip() {
  cout << "Testing Slice struct round trip... ";

  auto slice = ptr<Slice>();
  slice->l = 10;
  slice->u = 20;
  slice->step = 2;
  slice->wf = Prop{};

  FILE *temp = create_temp_file();
  if (!temp) {
    cout << "FAILED (could not create temp file)" << endl;
    return false;
  }

  if (!Slice_ser(temp, slice)) {
    cout << "FAILED (serialization failed)" << endl;
    fclose(temp);
    return false;
  }

  rewind(temp);
  Ptr<Slice> deserialized = Slice_des(temp);
  fclose(temp);

  if (deserialized->l != slice->l || deserialized->u != slice->u ||
      deserialized->step != slice->step) {
    cout << "FAILED (field mismatch)" << endl;
    return false;
  }

  cout << "PASSED" << endl;
  return true;
}

// Test APPair struct round trip
bool test_appair_roundtrip() {
  cout << "Testing APPair struct round trip... ";

  auto appair = ptr<APPair>();
  appair->step = -5;
  appair->num = 100;
  appair->offset = 200;

  FILE *temp = create_temp_file();
  if (!temp) {
    cout << "FAILED (could not create temp file)" << endl;
    return false;
  }

  if (!APPair_ser(temp, appair)) {
    cout << "FAILED (serialization failed)" << endl;
    fclose(temp);
    return false;
  }

  rewind(temp);
  Ptr<APPair> deserialized = APPair_des(temp);
  fclose(temp);

  if (deserialized->step != appair->step || deserialized->num != appair->num ||
      deserialized->offset != appair->offset) {
    cout << "FAILED (field mismatch)" << endl;
    return false;
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Index sum type round trip
bool test_index_roundtrip() {
  cout << "Testing Index sum type round trip... ";

  // Test coord variant
  {
    auto index = ptr<IndexCoordWrapper>();
    index->e = 42;

    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!Index_ser(temp, index)) {
      cout << "FAILED (coord serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    Ptr<Index> deserialized = Index_des(temp);
    fclose(temp);

    if (deserialized->tag != Index::Tag::coord) {
      cout << "FAILED (wrong tag for coord)" << endl;
      return false;
    }

    auto typed = static_cast<IndexCoordWrapper *>(deserialized.get());
    if (typed->e != 42) {
      cout << "FAILED (coord value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test DmaBounds sum type round trip
bool test_dmabounds_roundtrip() {
  cout << "Testing DmaBounds sum type round trip... ";

  // Test skip variant
  {
    auto bounds = ptr<DmaBoundsSkipWrapper>();

    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!DmaBounds_ser(temp, bounds)) {
      cout << "FAILED (skip serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    Ptr<DmaBounds> deserialized = DmaBounds_des(temp);
    fclose(temp);

    if (deserialized->tag != DmaBounds::Tag::skip) {
      cout << "FAILED (wrong tag for skip)" << endl;
      return false;
    }
  }

  // Test reg variant
  {
    auto bounds = ptr<DmaBoundsRegWrapper>();
    bounds->reg = 77;

    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!DmaBounds_ser(temp, bounds)) {
      cout << "FAILED (reg serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    Ptr<DmaBounds> deserialized = DmaBounds_des(temp);
    fclose(temp);

    if (deserialized->tag != DmaBounds::Tag::reg) {
      cout << "FAILED (wrong tag for reg)" << endl;
      return false;
    }

    auto typed = static_cast<DmaBoundsRegWrapper *>(deserialized.get());
    if (typed->reg != 77) {
      cout << "FAILED (reg value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test MatmulPerfMode enum round trip
bool test_matmulperfmode_roundtrip() {
  cout << "Testing MatmulPerfMode enum round trip... ";

  vector<MatmulPerfMode> test_values = {MatmulPerfMode::None,
                                        MatmulPerfMode::DoubleRow,
                                        MatmulPerfMode::DoubleRowSwInterleave};

  for (const MatmulPerfMode &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!MatmulPerfMode_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    MatmulPerfMode deserialized = MatmulPerfMode_des(temp);
    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test AccumCmd enum round trip
bool test_accumcmd_roundtrip() {
  cout << "Testing AccumCmd enum round trip... ";

  vector<AccumCmd> test_values = {
      AccumCmd::Idle, AccumCmd::Zero, AccumCmd::Accumulate,
      AccumCmd::ZeroAccumulate, AccumCmd::LoadAccumulate};

  for (const AccumCmd &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!AccumCmd_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    AccumCmd deserialized = AccumCmd_des(temp);
    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test ActivationFunc enum round trip
bool test_activationfunc_roundtrip() {
  cout << "Testing ActivationFunc enum round trip... ";

  vector<ActivationFunc> test_values = {
      ActivationFunc::abs,  ActivationFunc::relu, ActivationFunc::sigmoid,
      ActivationFunc::tanh, ActivationFunc::gelu, ActivationFunc::silu};

  for (const ActivationFunc &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!ActivationFunc_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    ActivationFunc deserialized = ActivationFunc_des(temp);
    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test TensorSubDim enum round trip
bool test_tensorsubdim_roundtrip() {
  cout << "Testing TensorSubDim enum round trip... ";

  vector<TensorSubDim> test_values = {TensorSubDim::X, TensorSubDim::XY,
                                      TensorSubDim::XYZ, TensorSubDim::XYZW};

  for (const TensorSubDim &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!TensorSubDim_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    TensorSubDim deserialized = TensorSubDim_des(temp);
    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test TransposeOps enum round trip
bool test_transposeops_roundtrip() {
  cout << "Testing TransposeOps enum round trip... ";

  vector<TransposeOps> test_values = {TransposeOps::None, TransposeOps::WZXY,
                                      TransposeOps::XYZW, TransposeOps::ZYXW};

  for (const TransposeOps &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!TransposeOps_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    TransposeOps deserialized = TransposeOps_des(temp);
    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test BrCmpOp enum round trip
bool test_brcmpop_roundtrip() {
  cout << "Testing BrCmpOp enum round trip... ";

  vector<BrCmpOp> test_values = {BrCmpOp::always, BrCmpOp::eq_imm,
                                 BrCmpOp::lt_reg, BrCmpOp::ge_imm};

  for (const BrCmpOp &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!BrCmpOp_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    BrCmpOp deserialized = BrCmpOp_des(temp);
    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test DataPattern struct round trip
bool test_datapattern_roundtrip() {
  cout << "Testing DataPattern struct round trip... ";

  auto pattern = ptr<DataPattern>();
  pattern->offset = -10;
  pattern->pattern = {}; // Empty APPair list for simplicity
  pattern->channelMultiplier = 2;

  FILE *temp = create_temp_file();
  if (!temp) {
    cout << "FAILED (could not create temp file)" << endl;
    return false;
  }

  if (!DataPattern_ser(temp, pattern)) {
    cout << "FAILED (serialization failed)" << endl;
    fclose(temp);
    return false;
  }

  rewind(temp);
  Ptr<DataPattern> deserialized = DataPattern_des(temp);
  fclose(temp);

  if (deserialized->offset != pattern->offset ||
      deserialized->channelMultiplier != pattern->channelMultiplier ||
      deserialized->pattern.size() != pattern->pattern.size()) {
    cout << "FAILED (field mismatch)" << endl;
    return false;
  }

  cout << "PASSED" << endl;
  return true;
}

// Test TensorHbm struct round trip
bool test_tensorhbm_roundtrip() {
  cout << "Testing TensorHbm struct round trip... ";

  auto tensor = ptr<TensorHbm>();
  tensor->name = "hbm_test";
  tensor->dtype = Dtype::float32;
  tensor->address = 0x12345678;
  tensor->dims = {}; // Empty APPair list for simplicity

  FILE *temp = create_temp_file();
  if (!temp) {
    cout << "FAILED (could not create temp file)" << endl;
    return false;
  }

  if (!TensorHbm_ser(temp, tensor)) {
    cout << "FAILED (serialization failed)" << endl;
    fclose(temp);
    return false;
  }

  rewind(temp);
  Ptr<TensorHbm> deserialized = TensorHbm_des(temp);
  fclose(temp);

  if (deserialized->name != tensor->name ||
      deserialized->dtype != tensor->dtype ||
      deserialized->address != tensor->address ||
      deserialized->dims.size() != tensor->dims.size()) {
    cout << "FAILED (field mismatch)" << endl;
    return false;
  }

  cout << "PASSED" << endl;
  return true;
}

// Test TensorSram struct round trip
bool test_tensorsram_roundtrip() {
  cout << "Testing TensorSram struct round trip... ";

  auto tensor = ptr<TensorSram>();
  tensor->name = "sram_test";
  tensor->dtype = Dtype::int32;
  tensor->parNum = 4;
  tensor->pattern = {}; // Empty APPair list for simplicity
  tensor->parOffset = 100;
  tensor->freeOffset = 200;

  FILE *temp = create_temp_file();
  if (!temp) {
    cout << "FAILED (could not create temp file)" << endl;
    return false;
  }

  if (!TensorSram_ser(temp, tensor)) {
    cout << "FAILED (serialization failed)" << endl;
    fclose(temp);
    return false;
  }

  rewind(temp);
  Ptr<TensorSram> deserialized = TensorSram_des(temp);
  fclose(temp);

  if (deserialized->name != tensor->name ||
      deserialized->dtype != tensor->dtype ||
      deserialized->parNum != tensor->parNum ||
      deserialized->parOffset != tensor->parOffset ||
      deserialized->freeOffset != tensor->freeOffset ||
      deserialized->pattern.size() != tensor->pattern.size()) {
    cout << "FAILED (field mismatch)" << endl;
    return false;
  }

  cout << "PASSED" << endl;
  return true;
}

// Test DropoutThresholdType enum round trip
bool test_dropoutthresholdtype_roundtrip() {
  cout << "Testing DropoutThresholdType enum round trip... ";

  vector<DropoutThresholdType> test_values = {DropoutThresholdType::DropRate,
                                              DropoutThresholdType::KeepRate};

  for (const DropoutThresholdType &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!DropoutThresholdType_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    DropoutThresholdType deserialized = DropoutThresholdType_des(temp);
    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test AffineSelectCmp enum round trip
bool test_affineselectcmp_roundtrip() {
  cout << "Testing AffineSelectCmp enum round trip... ";

  vector<AffineSelectCmp> test_values = {
      AffineSelectCmp::GreaterThan, AffineSelectCmp::GreaterThanEq,
      AffineSelectCmp::Eq, AffineSelectCmp::NotEq};

  for (const AffineSelectCmp &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!AffineSelectCmp_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    AffineSelectCmp deserialized = AffineSelectCmp_des(temp);
    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test TensorScalarReverseOps enum round trip
bool test_tensorscalarreverseops_roundtrip() {
  cout << "Testing TensorScalarReverseOps enum round trip... ";

  vector<TensorScalarReverseOps> test_values = {
      TensorScalarReverseOps::none, TensorScalarReverseOps::first,
      TensorScalarReverseOps::second, TensorScalarReverseOps::both};

  for (const TensorScalarReverseOps &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!TensorScalarReverseOps_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    TensorScalarReverseOps deserialized = TensorScalarReverseOps_des(temp);
    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test PrintOutputBuffer enum round trip
bool test_printoutputbuffer_roundtrip() {
  cout << "Testing PrintOutputBuffer enum round trip... ";

  vector<PrintOutputBuffer> test_values = {PrintOutputBuffer::stdout,
                                           PrintOutputBuffer::stderr};

  for (const PrintOutputBuffer &original : test_values) {
    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!PrintOutputBuffer_ser(temp, original)) {
      cout << "FAILED (serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    PrintOutputBuffer deserialized = PrintOutputBuffer_des(temp);
    fclose(temp);

    if (original != deserialized) {
      cout << "FAILED (value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test Operand sum type round trip
bool test_operand_roundtrip() {
  cout << "Testing Operand sum type round trip... ";

  // Test imm variant
  {
    auto operand = ptr<OperandImmWrapper>();
    operand->i = ptr<ImmediateIntWrapper>();
    static_cast<ImmediateIntWrapper *>(operand->i.get())->i = 42;

    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!Operand_ser(temp, operand)) {
      cout << "FAILED (imm serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    Ptr<Operand> deserialized = Operand_des(temp);
    fclose(temp);

    if (deserialized->tag != Operand::Tag::imm) {
      cout << "FAILED (wrong tag for imm)" << endl;
      return false;
    }
  }

  // Test tile variant
  {
    auto operand = ptr<OperandTileWrapper>();
    operand->t = ptr<TensorRefRegisterWrapper>();
    static_cast<TensorRefRegisterWrapper *>(operand->t.get())->reg = 99;

    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!Operand_ser(temp, operand)) {
      cout << "FAILED (tile serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    Ptr<Operand> deserialized = Operand_des(temp);
    fclose(temp);

    if (deserialized->tag != Operand::Tag::tile) {
      cout << "FAILED (wrong tag for tile)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test IndexMissBehavior sum type round trip
bool test_indexmissbehavior_roundtrip() {
  cout << "Testing IndexMissBehavior sum type round trip... ";

  // Test skip variant
  {
    auto behavior = ptr<IndexMissBehaviorSkipWrapper>();

    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!IndexMissBehavior_ser(temp, behavior)) {
      cout << "FAILED (skip serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    Ptr<IndexMissBehavior> deserialized = IndexMissBehavior_des(temp);
    fclose(temp);

    if (deserialized->tag != IndexMissBehavior::Tag::skip) {
      cout << "FAILED (wrong tag for skip)" << endl;
      return false;
    }
  }

  // Test imm variant
  {
    auto behavior = ptr<IndexMissBehaviorImmWrapper>();
    behavior->value = ptr<ImmediateIntWrapper>();
    static_cast<ImmediateIntWrapper *>(behavior->value.get())->i = 123;

    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!IndexMissBehavior_ser(temp, behavior)) {
      cout << "FAILED (imm serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    Ptr<IndexMissBehavior> deserialized = IndexMissBehavior_des(temp);
    fclose(temp);

    if (deserialized->tag != IndexMissBehavior::Tag::imm) {
      cout << "FAILED (wrong tag for imm)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test ReplicaGroup sum type round trip
bool test_replicagroup_roundtrip() {
  cout << "Testing ReplicaGroup sum type round trip... ";

  // Test unspecified variant
  {
    auto group = ptr<ReplicaGroupUnspecifiedWrapper>();

    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!ReplicaGroup_ser(temp, group)) {
      cout << "FAILED (unspecified serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    Ptr<ReplicaGroup> deserialized = ReplicaGroup_des(temp);
    fclose(temp);

    if (deserialized->tag != ReplicaGroup::Tag::unspecified) {
      cout << "FAILED (wrong tag for unspecified)" << endl;
      return false;
    }
  }

  // Test named variant
  {
    auto group = ptr<ReplicaGroupNamedWrapper>();
    group->name = "test_group";

    FILE *temp = create_temp_file();
    if (!temp) {
      cout << "FAILED (could not create temp file)" << endl;
      return false;
    }

    if (!ReplicaGroup_ser(temp, group)) {
      cout << "FAILED (named serialization failed)" << endl;
      fclose(temp);
      return false;
    }

    rewind(temp);
    Ptr<ReplicaGroup> deserialized = ReplicaGroup_des(temp);
    fclose(temp);

    if (deserialized->tag != ReplicaGroup::Tag::named) {
      cout << "FAILED (wrong tag for named)" << endl;
      return false;
    }

    auto typed = static_cast<ReplicaGroupNamedWrapper *>(deserialized.get());
    if (typed->name != "test_group") {
      cout << "FAILED (name value mismatch)" << endl;
      return false;
    }
  }

  cout << "PASSED" << endl;
  return true;
}

// Test simple Kernel round trip
bool test_kernel_roundtrip() {
  cout << "Testing Kernel round trip... ";

  auto kernel = ptr<Kernel>();
  kernel->name = "test_kernel";

  // Create a simple input tensor
  auto inputTensor = ptr<TensorName>();
  inputTensor->name = "input";
  inputTensor->dtype = Dtype::float32;
  inputTensor->freeElements = 1024;
  inputTensor->addressRotation = false;

  // Create shape
  auto shape = ptr<Shape>();
  shape->parDim = 1;
  shape->freeDims.push_back(32);
  shape->freeDims.push_back(32);
  inputTensor->shape = shape;

  // Create address
  auto address = ptr<Address>();
  address->name = "input_addr";
  address->memory = Memory::hbm;
  address->parSize = 1;
  address->freeSize = 1024;
  address->parOffset = Option<Nat>();
  address->freeOffset = Option<Nat>();
  address->isShared = false;
  inputTensor->address = address;

  // Set WF props (empty for now)
  inputTensor->parWF = Prop{};
  inputTensor->freeWF = Prop{};

  kernel->inputs.push_back(inputTensor);
  kernel->outputs = {}; // Empty outputs for simplicity

  // Create a simple block
  auto block = ptr<Block>();
  block->label = "main";
  block->body = {}; // Empty body for simplicity
  kernel->body.push_back(block);

  FILE *temp = create_temp_file();
  if (!temp) {
    cout << "FAILED (could not create temp file)" << endl;
    return false;
  }

  // Serialize
  if (!Kernel_ser(temp, kernel)) {
    cout << "FAILED (serialization failed)" << endl;
    fclose(temp);
    return false;
  }

  // Reset file position
  rewind(temp);

  // Deserialize
  Ptr<Kernel> deserialized = Kernel_des(temp);

  fclose(temp);

  // Check kernel name
  if (deserialized->name != kernel->name) {
    cout << "FAILED (kernel name mismatch)" << endl;
    return false;
  }

  // Check inputs
  if (deserialized->inputs.size() != 1) {
    cout << "FAILED (inputs size mismatch)" << endl;
    return false;
  }

  auto firstInput = deserialized->inputs.front();
  if (firstInput->name != "input" || firstInput->dtype != Dtype::float32) {
    cout << "FAILED (input tensor mismatch)" << endl;
    return false;
  }

  // Check body
  if (deserialized->body.size() != 1) {
    cout << "FAILED (body size mismatch)" << endl;
    return false;
  }

  auto firstBlock = deserialized->body.front();
  if (firstBlock->label != "main") {
    cout << "FAILED (body mismatch)" << endl;
    return false;
  }

  cout << "PASSED" << endl;
  return true;
}

int main() {
  cout << "Running KLIR serialization/deserialization round trip tests..."
       << endl
       << endl;

  int passed = 0;
  int total = 0;

  // Run all tests
  if (test_option_bool_roundtrip())
    passed++;
  total++;

  if (test_option_nat_roundtrip())
    passed++;
  total++;

  if (test_option_string_roundtrip())
    passed++;
  total++;

  if (test_list_bool_roundtrip())
    passed++;
  total++;

  if (test_list_string_roundtrip())
    passed++;
  total++;

  if (test_option_list_nat_roundtrip())
    passed++;
  total++;

  if (test_pos_roundtrip())
    passed++;
  total++;

  if (test_memory_roundtrip())
    passed++;
  total++;

  if (test_dtype_roundtrip())
    passed++;
  total++;

  if (test_engine_roundtrip())
    passed++;
  total++;

  if (test_aluop_roundtrip())
    passed++;
  total++;

  if (test_immediate_roundtrip())
    passed++;
  total++;

  if (test_tensorref_roundtrip())
    passed++;
  total++;

  if (test_slice_roundtrip())
    passed++;
  total++;

  if (test_appair_roundtrip())
    passed++;
  total++;

  if (test_index_roundtrip())
    passed++;
  total++;

  if (test_dmabounds_roundtrip())
    passed++;
  total++;

  if (test_matmulperfmode_roundtrip())
    passed++;
  total++;

  if (test_accumcmd_roundtrip())
    passed++;
  total++;

  if (test_activationfunc_roundtrip())
    passed++;
  total++;

  if (test_tensorsubdim_roundtrip())
    passed++;
  total++;

  if (test_transposeops_roundtrip())
    passed++;
  total++;

  if (test_brcmpop_roundtrip())
    passed++;
  total++;

  if (test_datapattern_roundtrip())
    passed++;
  total++;

  if (test_tensorhbm_roundtrip())
    passed++;
  total++;

  if (test_tensorsram_roundtrip())
    passed++;
  total++;

  if (test_dropoutthresholdtype_roundtrip())
    passed++;
  total++;

  if (test_affineselectcmp_roundtrip())
    passed++;
  total++;

  if (test_tensorscalarreverseops_roundtrip())
    passed++;
  total++;

  if (test_printoutputbuffer_roundtrip())
    passed++;
  total++;

  if (test_operand_roundtrip())
    passed++;
  total++;

  if (test_indexmissbehavior_roundtrip())
    passed++;
  total++;

  if (test_replicagroup_roundtrip())
    passed++;
  total++;

  if (test_shape_roundtrip())
    passed++;
  total++;

  if (test_address_roundtrip())
    passed++;
  total++;

  if (test_tensor_name_roundtrip())
    passed++;
  total++;

  if (test_operator_register_move_roundtrip())
    passed++;
  total++;

  if (test_all_operators_roundtrip())
    passed++;
  total++;

  if (test_stmt_roundtrip())
    passed++;
  total++;

  if (test_block_roundtrip())
    passed++;
  total++;

  if (test_kernel_roundtrip())
    passed++;
  total++;

  cout << endl
       << "Results: " << passed << "/" << total << " tests passed" << endl;

  if (passed == total) {
    cout << "All tests PASSED!" << endl;
    return 0;
  } else {
    cout << "Some tests FAILED!" << endl;
    return 1;
  }
}