import Lean

/- A GensymEnv contains the state necessary to generate unique names
   for variables in a compilation context

TODO: this could be made more ergonomic by using a monad transformer -/
structure GensymEnv where
  gensymCounter : Nat := 0
  gensymUsed : Std.HashSet String := default
  deriving Inhabited, Repr

/- Generates a new unique name based on the suggestion, returning the updated
state and the new name.
If the suggestion is not already used, it is returned directly. Otherwise, a
new name is generated in the form "gs_<counter>" where <counter> is incremented
until a unique name is found. -/
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
