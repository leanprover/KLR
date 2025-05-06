/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

namespace KLR.Util.Gzip

@[extern "lean_gzip"]
opaque gzip (bytes : @&ByteArray) : ByteArray

end KLR.Util.Gzip
