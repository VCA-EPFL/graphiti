/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.TypeExpr

namespace Graphiti.TypeExpr.Parser.Test

/-- info: true -/
#guard_msgs in
#eval parseTypeExpr " ( Bool ×   ( T × T))"
  == some (.pair .bool (.pair .nat .nat))

/-- info: true -/
#guard_msgs in
#eval flatten_type <$> parseTypeExpr " ( Bool ×   ( T × T))"
  == some [.bool, .nat, .nat]

/-- info: true -/
#guard_msgs in
#eval toString (TypeExpr.pair .bool (.pair .nat .nat))
  == "(Bool × (T × T))"

/-- info: true -/
#guard_msgs in
#eval toString (parseTypeExpr "(((T × T) × (T × T)) × (T × Bool))")
  == "(some (((T × T) × (T × T)) × (T × Bool)))"

/-- info: true -/
#guard_msgs in
#eval (parseNode ("split (T × (Bool × (T × T))) Bool")).get!.2[0]!
  == .type_arg (.pair (.nat) (.pair (.bool) (.pair (.nat) (.nat))))

/-- info: true -/
#guard_msgs in
#eval (parseNode ("branch (T × T)")).get!.2[0]!
  == .type_arg (.pair (.nat) (.nat))

/-- info: true -/
#guard_msgs in
#eval (parseNode ("join T (TagT × Bool)")).get!.2[1]!
  == .type_arg (.pair (.unit) (.bool))

/-- info: true -/
#guard_msgs in
#eval (parseNode ("mux (T × (T × Bool))")).get!.2[0]!
  == .type_arg (.pair (.nat) (.pair (.nat) (.bool)))

end Graphiti.TypeExpr.Parser.Test
