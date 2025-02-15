"""
Copyright (C) 2025, Amazon.com. All Rights Reserved

"""
import types

# Define APIs needed by test cases. We don't need the "real" versions
# of these modules, we just want their names to be recognized as
# modules so accesses to their contents will show up as undefined
# names. The lean code can then deal with all of the fully-qualified
# undefined names, e.g. `nki.isa.tensor_scalar`.

np = numpy = types.ModuleType('numpy')
nki = types.ModuleType('nki')
nisa = nki.isa = types.ModuleType('nki.isa')
nl = nki.language = types.ModuleType('nki.language')
