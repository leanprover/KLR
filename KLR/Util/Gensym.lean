import Lean

structure GensymEnv where
  gensymCounter : Nat := 0
  gensymUsed : Std.HashSet String := default
  deriving Inhabited, Repr

partial def GensymEnv.gensym (env : GensymEnv) (suggestion : String) : (String × GensymEnv) := Id.run do
  let mut env := env
  if !env.gensymUsed.contains suggestion then
    env := {env with gensymUsed := env.gensymUsed.insert suggestion }
    return (suggestion, env)

  let mut name := s!"gs_{env.gensymCounter}"
  repeat do
    if !env.gensymUsed.contains name then
      env := { env with gensymUsed := env.gensymUsed.insert name, gensymCounter := env.gensymCounter + 1 }
      break
    else
      env := { env with gensymCounter := env.gensymCounter + 1 }
      name := s!"gs_{env.gensymCounter}"
  (name, env)
