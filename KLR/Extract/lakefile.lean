import Lake
open Lake DSL

package "Extract" where

require KLR from "../.."

@[default_target]
lean_lib "Extract" where
