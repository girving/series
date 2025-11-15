import Lean

/-!
# `qsimp`: Quiet `simp`

A version of `simp` that suppresses the `unusedSimpArgs` linter.
-/

syntax "qsimp" "[" Lean.Parser.Tactic.simpArg,* "]" : tactic

macro_rules
  | `(tactic| qsimp [ $args,* ]) =>
    `(tactic| set_option linter.unusedSimpArgs false in simp [ $args,* ])
