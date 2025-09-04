#pragma once

#include "klir_ast.hpp"
#include "klir_common.hpp"
#include <variant>
#include <string>
#include <vector>
#include <optional>

namespace Trace {

struct Error {
    std::string msg;
    Error(std::string&& m) : msg(std::move(m)) {}
};

// Simple error handling
template<typename T>
using TraceResult = std::variant<T, Error>;

template<typename T>
bool is_ok(const TraceResult<T>& result) {
    return std::holds_alternative<T>(result);
}

template<typename T>
T get_ok(const TraceResult<T>& result) {
    return std::get<T>(result);
}

Error TraceError(std::string msg) {
    return Error{std::move(msg)};
}


struct Term;

struct Builtin final { std::string name; std::optional<Term*> term; };
struct Ref final {
     std::string name;
     enum Kind {
        list,
        dict,
        object,
     };
     Kind kind;
};

// TODO move this to NKI namespace once it exists
struct Fun final {
    std::string name;
    std::string file;
    size_t line;
    std::string source;
    // FIXME: uncomment once implemented
    // std::vector<KLR::Core::Stmt> body;
    // std::vector<KLR::Core::Param> args;
};

struct Var final { std::string name; };

struct Slice final {
    std::optional<int> start;
    std::optional<int> stop;
    std::optional<int> step;
};

struct MgItem {
    int x, y, z;
};

struct Term final {
    enum Kind {
        // Internals
        Module, Builtin, Ref, Source,
        // Expressions / values
        Var, None, Bool, Int, Float, String, Access, Tuple, List, Tensor,
        // Indexing
        Elipsis, Slice, Pointer, Mgrid, MgItem
    } kind;
    
    std::variant<
        std::string, // used with module, var, string
        struct Builtin, struct Ref, struct Fun,
        struct Var,
        std::monostate, // used with None, Elipsis, Mgrid
        bool, int, float, struct Slice, klr::Address,
        std::vector<Term>, // used with List, Tuple
        klr::Access // used with Access
        // TODO to support Tensor we need some type that would implement it
        // we might want to use python's native type wrapped in well understood
        // type definition
    > data;
    
    std::string kindStr() const {
        switch(kind) {
            case Module: return "Module";
            case Builtin: return "Builtin";
            case Ref: return "Ref";
            case Source: return "Source";
            case Var: return "Var";
            case None: return "None";
            case Bool: return "Bool";
            case Int: return "Int";
            case Float: return "Float";
            case String: return "String";
            case Access: return "Access";
            case Tuple: return "Tuple";
            case List: return "List";
            case Tensor: return "Tensor";
            case Elipsis: return "Elipsis";
            case Slice: return "Slice";
            case Pointer: return "Pointer";
            case Mgrid: return "Mgrid";
            case MgItem: return "MgItem";
            default: return "Unknown";
        }
    }
};

template<typename T>
struct FromNKI {
    static TraceResult<T> fromNKI(const Term& t);
};

template<typename T>
T fromNKI_with_default(const Term& t, const T& default_value) {
    auto result = FromNKI<T>::fromNKI(t);
    return is_ok(result) ? get_ok(result) : default_value;
}

template<typename T>
struct FromNKI<std::vector<T>> {
    static TraceResult<std::vector<T>> fromNKI(const Term& t) {
        if (t.kind == Term::List || t.kind == Term::Tuple) {
            const auto& list = std::get<std::vector<Term>>(t.data);
            std::vector<T> result;
            for (const auto& item : list) {
                auto itemResult = FromNKI<T>::fromNKI(item);
                if (!is_ok(itemResult)) {
                    return std::get<Error>(itemResult);
                }
                result.push_back(get_ok(itemResult));
            }
            return result;
        }
        return TraceError("expecting sequence ('list' or 'tuple'), got '" + t.kindStr() + "'");
    }
};

template<typename T>
struct FromNKI<std::optional<T>> {
    static TraceResult<std::optional<T>> fromNKI(const Term& t) {
        if (t.kind == Term::None) {
            return std::optional<T>{};
        }
        auto result = FromNKI<T>::fromNKI(t);
        if (is_ok(result)) {
            return std::optional<T>{get_ok(result)};
        }
        return std::get<Error>(result);
    }
};

template<typename A, typename B>
struct FromNKI<std::variant<A, B>> {
    static TraceResult<std::variant<A, B>> fromNKI(const Term& t) {
        auto resultA = FromNKI<A>::fromNKI(t);
        if (is_ok(resultA)) {
            return std::variant<A, B>{get_ok(resultA)};
        }
        auto resultB = FromNKI<B>::fromNKI(t);
        if (is_ok(resultB)) {
            return std::variant<A, B>{get_ok(resultB)};
        }
        return TraceError("cannot convert to either type in sum: " + std::get<Error>(resultB).msg);
    }
};

template<typename A, typename B>
struct FromNKI<std::pair<A, B>> {
    static TraceResult<std::pair<A, B>> fromNKI(const Term& t) {
        if (t.kind == Term::List || t.kind == Term::Tuple) {
            const auto& list = std::get<std::vector<Term>>(t.data);
            if (list.size() == 2) {
                auto resultA = FromNKI<A>::fromNKI(list[0]);
                if (!is_ok(resultA)) {
                    return std::get<Error>(resultA);
                }
                auto resultB = FromNKI<B>::fromNKI(list[1]);
                if (!is_ok(resultB)) {
                    return std::get<Error>(resultB);
                }
                return std::pair<A, B>{get_ok(resultA), get_ok(resultB)};
            }
        }
        return TraceError("expecting 'pair', got '" + t.kindStr() + "'");
    }
};

template<>
struct FromNKI<bool> {
    static TraceResult<bool> fromNKI(const Term& t) {
        if (t.kind == Term::Bool) {
            return std::get<bool>(t.data);
        }
        return TraceError("expecting 'boolean', got '" + t.kindStr() + "'");
    }
};

template<>
struct FromNKI<int> {
    static TraceResult<int> fromNKI(const Term& t) {
        if (t.kind == Term::Bool) {
            return std::get<bool>(t.data) ? 1 : 0;
        }
        if (t.kind == Term::Int) {
            return std::get<int>(t.data);
        }
        return TraceError("expecting 'integer', got '" + t.kindStr() + "'");
    }
};

template<>
struct FromNKI<float> {
    static TraceResult<float> fromNKI(const Term& t) {
        if (t.kind == Term::Bool) {
            return std::get<bool>(t.data) ? 1.0f : 0.0f;
        }
        if (t.kind == Term::Int) {
            return static_cast<float>(std::get<int>(t.data));
        }
        if (t.kind == Term::Float) {
            return std::get<float>(t.data);
        }
        return TraceError("expecting 'float', got '" + t.kindStr() + "'");
    }
};

template<>
struct FromNKI<std::string> {
    static TraceResult<std::string> fromNKI(const Term& t) {
        if (t.kind == Term::String) {
            return std::get<std::string>(t.data);
        }
        return TraceError("expecting 'string', got '" + t.kindStr() + "'");
    }
};

template<>
struct FromNKI<uint32_t> {
    static TraceResult<uint32_t> fromNKI(const Term& t) {
        if (t.kind == Term::Bool) {
            return std::get<bool>(t.data) ? 1u : 0u;
        }
        if (t.kind == Term::Int) {
            int val = std::get<int>(t.data);
            if (val < 0) {
                return TraceError("negative value cannot be converted to uint32_t");
            }
            return static_cast<uint32_t>(val);
        }
        return TraceError("expecting 'integer', got '" + t.kindStr() + "'");
    }
};

template<>
struct FromNKI<klr::Immediate> {
    static TraceResult<klr::Immediate> fromNKI(const Term& t) {
        if (t.kind == Term::Bool) {
            auto imm = klr::ImmediateIntWrapper();
            imm.i = std::get<bool>(t.data) ? 1 : 0;
            return imm;
        }
        if (t.kind == Term::Int) {
            auto imm = klr::ImmediateIntWrapper();
            imm.i = std::get<int>(t.data);
            return imm;
        }
        if (t.kind == Term::Float) {
            auto imm = klr::ImmediateFloatWrapper();
            imm.f = std::get<float>(t.data);
            return imm;
        }
        return TraceError("expecting int or 'float', got '" + t.kindStr() + "'");
    }
};

template<>
struct FromNKI<klr::Shape> {
    static TraceResult<klr::Shape> fromNKI(const Term& t) {
        auto listResult = FromNKI<std::vector<uint32_t>>::fromNKI(t);
        if (!is_ok(listResult)) {
            return std::get<Error>(listResult);
        }
        const auto& list = get_ok(listResult);
        if (list.empty()) {
            return TraceError("invalid shape");
        }
        klr::Shape shape;
        shape.parDim = list[0];
        shape.freeDims = std::list<uint32_t>(list.begin() + 1, list.end());
        return shape;
    }
};

template<>
struct FromNKI<klr::Access> {
    static TraceResult<klr::Access> fromNKI(const Term& t) {
        if (t.kind == Term::Access) {
            return std::get<klr::Access>(t.data);
        } else {
            return TraceError("expecting access");
        }
    }
};

template<>
struct FromNKI<klr::TensorName> {
    static TraceResult<klr::TensorName> fromNKI(const Term& t) {
        if (t.kind == Term::Access) {
            auto ac = std::get<klr::Access>(t.data);
            if (ac.tag == klr::Access::Tag::simple) {
                // return ac.simple
                // FIXME actually return simple access. Seems to be not matching lean
            }
            return TraceError("expecting simple access");
        } else {
            return TraceError("expecting access");
        }
    }
};

template<>
struct FromNKI<klr::Address> {
    static TraceResult<klr::Address> fromNKI(const Term& t) {
        if (t.kind == Term::Pointer) {
            return std::get<klr::Address>(t.data);
        }
        return TraceError("expecting pointer");
    }
};

template<>
struct FromNKI<klr::Dtype> {
    static TraceResult<klr::Dtype> fromNKI(const Term& t) {
        if (t.kind == Term::Var) {
            const auto& name = std::get<Var>(t.data).name;
            if (name == "neuronxcc.nki.language.uint8") return klr::Dtype::uint8;
            if (name == "neuronxcc.nki.language.int8") return klr::Dtype::int8;
            if (name == "neuronxcc.nki.language.uint16") return klr::Dtype::uint16;
            if (name == "neuronxcc.nki.language.int16") return klr::Dtype::int16;
            if (name == "neuronxcc.nki.language.uint32") return klr::Dtype::uint32;
            if (name == "neuronxcc.nki.language.int32") return klr::Dtype::int32;
            if (name == "neuronxcc.nki.language.float8e3") return klr::Dtype::float8e3;
            if (name == "neuronxcc.nki.language.float8e4") return klr::Dtype::float8e4;
            if (name == "neuronxcc.nki.language.float8e5") return klr::Dtype::float8e5;
            if (name == "neuronxcc.nki.language.float8_e4m3") return klr::Dtype::float8e4;
            if (name == "neuronxcc.nki.language.float8_e5m2") return klr::Dtype::float8e5;
            if (name == "neuronxcc.nki.language.float16") return klr::Dtype::float16;
            if (name == "neuronxcc.nki.language.bfloat16") return klr::Dtype::bfloat16;
            if (name == "neuronxcc.nki.language.tfloat32") return klr::Dtype::float32r;
            if (name == "neuronxcc.nki.language.float32") return klr::Dtype::float32;
            if (name == "neuronxcc.nki.language.bool_") return klr::Dtype::uint8;
            if (name == "numpy.uint8") return klr::Dtype::uint8;
            if (name == "numpy.int8") return klr::Dtype::int8;
            if (name == "numpy.uint16") return klr::Dtype::uint16;
            if (name == "numpy.int16") return klr::Dtype::int16;
            if (name == "numpy.uint32") return klr::Dtype::uint32;
            if (name == "numpy.int32") return klr::Dtype::int32;
            if (name == "numpy.float16") return klr::Dtype::float16;
            if (name == "numpy.float32") return klr::Dtype::float32;
            if (name == "numpy.bool") return klr::Dtype::uint8;
            return TraceError("unsupported dtype '" + name + "'");
        }
        if (t.kind == Term::String) {
            const auto& name = std::get<std::string>(t.data);
            if (name == "uint8") return klr::Dtype::uint8;
            if (name == "int8") return klr::Dtype::int8;
            if (name == "uint16") return klr::Dtype::uint16;
            if (name == "int16") return klr::Dtype::int16;
            if (name == "uint32") return klr::Dtype::uint32;
            if (name == "int32") return klr::Dtype::int32;
            if (name == "float8e3") return klr::Dtype::float8e3;
            if (name == "float8e4") return klr::Dtype::float8e4;
            if (name == "float8e5") return klr::Dtype::float8e5;
            if (name == "float8_e4m3") return klr::Dtype::float8e4;
            if (name == "float8_e5m2") return klr::Dtype::float8e5;
            if (name == "float16") return klr::Dtype::float16;
            if (name == "bfloat16") return klr::Dtype::bfloat16;
            if (name == "tfloat32") return klr::Dtype::float32r;
            if (name == "float32") return klr::Dtype::float32;
            if (name == "bool") return klr::Dtype::uint8;
            return TraceError("unsupported dtype '" + name + "'");
        }
        return TraceError("expecting 'dtype', got '" + t.kindStr() + "'");
    }
};

template<>
struct FromNKI<klr::Memory> {
    static TraceResult<klr::Memory> fromNKI(const Term& t) {
        if (t.kind == Term::Var) {
            const auto& name = std::get<Var>(t.data).name;
            if (name == "neuronxcc.nki.language.shared_hbm") return klr::Memory::hbm;
            if (name == "neuronxcc.nki.language.private_hbm") return klr::Memory::hbm;
            if (name == "neuronxcc.nki.language.hbm") return klr::Memory::hbm;
            if (name == "neuronxcc.nki.language.sbuf") return klr::Memory::sbuf;
            if (name == "neuronxcc.nki.language.psum") return klr::Memory::psum;
        } else if (t.kind == Term::Pointer) {
            return std::get<klr::Address>(t.data).memory;
        }
        return TraceError("expecting buffer type");
    }
};

template<>
struct FromNKI<klr::Engine> {
    static TraceResult<klr::Engine> fromNKI(const Term& t) {
        if (t.kind == Term::Var) {
            const auto& name = std::get<Var>(t.data).name;
            if (name == "neuronxcc.nki.isa.unknown_engine") return klr::Engine::unassigned;
            if (name == "neuronxcc.nki.isa.tensor_engine") return klr::Engine::pe;
            if (name == "neuronxcc.nki.isa.vector_engine") return klr::Engine::dve;
            if (name == "neuronxcc.nki.isa.scalar_engine") return klr::Engine::sp;
        }
        return TraceError("expecting engine type");
    }
};

template<>
struct FromNKI<klr::AluOp> {
    static TraceResult<klr::AluOp> fromNKI(const Term& t) {
        if (t.kind == Term::None) return klr::AluOp::bypass;
        if (t.kind == Term::Var) {
            const auto& name = std::get<Var>(t.data).name;
            if (name == "neuronxcc.nki.language.add" || name == "numpy.add") return klr::AluOp::add;
            if (name == "neuronxcc.nki.language.subtract" || name == "numpy.subtract") return klr::AluOp::subtract;
            if (name == "neuronxcc.nki.language.multiply" || name == "numpy.multiply") return klr::AluOp::mult;
            if (name == "neuronxcc.nki.language.maximum" || name == "numpy.maximum") return klr::AluOp::max;
            if (name == "neuronxcc.nki.language.minimum" || name == "numpy.minimum") return klr::AluOp::min;
            if (name == "neuronxcc.nki.language.equal" || name == "numpy.equal") return klr::AluOp::is_equal;
            if (name == "neuronxcc.nki.language.not_equal" || name == "numpy.not_equal") return klr::AluOp::not_equal;
            if (name == "neuronxcc.nki.language.greater_equal" || name == "numpy.greater_equal") return klr::AluOp::is_ge;
            if (name == "neuronxcc.nki.language.greater" || name == "numpy.greater") return klr::AluOp::is_gt;
            if (name == "neuronxcc.nki.language.less_equal" || name == "numpy.less_equal") return klr::AluOp::is_le;
            if (name == "neuronxcc.nki.language.less" || name == "numpy.less") return klr::AluOp::is_lt;
            if (name == "neuronxcc.nki.language.logical_not" || name == "numpy.logical_not") return TraceError("'logical_not' not supported");
            if (name == "neuronxcc.nki.language.logical_and" || name == "numpy.logical_and") return klr::AluOp::logical_and;
            if (name == "neuronxcc.nki.language.logical_or" || name == "numpy.logical_or") return klr::AluOp::logical_or;
            if (name == "neuronxcc.nki.language.logical_xor" || name == "numpy.logical_xor") return klr::AluOp::logical_xor;
            if (name == "neuronxcc.nki.language.bitwise_and" || name == "numpy.bitwise_and") return klr::AluOp::bitwise_and;
            if (name == "neuronxcc.nki.language.bitwise_or" || name == "numpy.bitwise_or") return klr::AluOp::bitwise_or;
            if (name == "neuronxcc.nki.language.bitwise_xor" || name == "numpy.bitwise_xor") return klr::AluOp::bitwise_xor;
            if (name == "neuronxcc.nki.language.invert" || name == "numpy.bitwise_not" || name == "numpy.bitwise_invert") return klr::AluOp::bitwise_not;
            if (name == "neuronxcc.nki.language.left_shift" || name == "numpy.bitwise_left_shift") return klr::AluOp::logical_shift_left;
            if (name == "neuronxcc.nki.language.right_shift" || name == "numpy.bitwise_right_shift") return klr::AluOp::logical_shift_right;
            return TraceError("unsupported operator " + name);
        }
        return TraceError("expecting operator, got '" + t.kindStr() + "'");
    }
};

template<>
struct FromNKI<klr::ActivationFunc> {
    static TraceResult<klr::ActivationFunc> fromNKI(const Term& t) {
        if (t.kind == Term::Var) {
            const auto& name = std::get<Var>(t.data).name;
            if (name == "neuronxcc.nki.language.copy" || name == "numpy.copy") return klr::ActivationFunc::copy;
            if (name == "neuronxcc.nki.language.square" || name == "numpy.square") return klr::ActivationFunc::square;
            if (name == "neuronxcc.nki.language.sigmoid") return klr::ActivationFunc::sigmoid;
            if (name == "neuronxcc.nki.language.relu") return klr::ActivationFunc::relu;
            if (name == "neuronxcc.nki.language.gelu") return klr::ActivationFunc::gelu;
            if (name == "neuronxcc.nki.language.gelu_dx") return klr::ActivationFunc::gelu_dx;
            if (name == "neuronxcc.nki.language.gelu_apprx_tanh") return klr::ActivationFunc::gelu_apprx_tanh;
            if (name == "neuronxcc.nki.language.silu") return klr::ActivationFunc::silu;
            if (name == "neuronxcc.nki.language.silu_dx") return klr::ActivationFunc::silu_dx;
            if (name == "neuronxcc.nki.language.tanh" || name == "numpy.tanh") return klr::ActivationFunc::tanh;
            if (name == "neuronxcc.nki.language.softplus") return klr::ActivationFunc::softplus;
            if (name == "neuronxcc.nki.language.mish") return klr::ActivationFunc::mish;
            if (name == "neuronxcc.nki.language.erf") return klr::ActivationFunc::erf;
            if (name == "neuronxcc.nki.language.erf_dx") return klr::ActivationFunc::erf_dx;
            if (name == "neuronxcc.nki.language.exp" || name == "numpy.exp") return klr::ActivationFunc::exp;
            if (name == "neuronxcc.nki.language.log" || name == "numpy.log") return klr::ActivationFunc::log;
            if (name == "neuronxcc.nki.language.sin" || name == "numpy.sin") return klr::ActivationFunc::sin;
            if (name == "neuronxcc.nki.language.arctan" || name == "numpy.arctan") return klr::ActivationFunc::arctan;
            if (name == "neuronxcc.nki.language.sqrt" || name == "numpy.sqrt") return klr::ActivationFunc::sqrt;
            if (name == "neuronxcc.nki.language.rsqrt") return klr::ActivationFunc::rsqrt;
            if (name == "neuronxcc.nki.language.reciprocal" || name == "numpy.reciprocal") return klr::ActivationFunc::reciprocal;
            if (name == "neuronxcc.nki.language.sign" || name == "numpy.sign") return klr::ActivationFunc::sign;
            if (name == "neuronxcc.nki.language.abs" || name == "numpy.abs") return klr::ActivationFunc::abs;
        }
        return TraceError("expecting activation function type");
    }
};

template<>
struct FromNKI<klr::AccumCmd> {
    static TraceResult<klr::AccumCmd> fromNKI(const Term& t) {
        if (t.kind == Term::Var) {
            const auto& name = std::get<Var>(t.data).name;
            if (name == "neuronxcc.nki.isa.reduce_cmd.idle") return klr::AccumCmd::Idle;
            if (name == "neuronxcc.nki.isa.reduce_cmd.reset") return klr::AccumCmd::Zero;
            if (name == "neuronxcc.nki.isa.reduce_cmd.reduce") return klr::AccumCmd::Accumulate;
            if (name == "neuronxcc.nki.isa.reduce_cmd.reset_reduce") return klr::AccumCmd::ZeroAccumulate;
        }
        return TraceError("expecting activation function type");
    }
};

}