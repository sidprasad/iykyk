module

public import Iykyk

public section

/-!
# Productive-rule and inconsistency examples
-/

namespace Iykyk.Examples.Bounded

set_option linter.unusedVariables false

variable {Vertex : Type}
variable (Reach : Vertex → Prop)

-- A rule chain longer than `maxRounds` still converges: the first saturation pass runs out of
-- rounds, the second resumes where it stopped and reaches a fixpoint. Only the final pass decides
-- the status, so a run that genuinely finished is reported `complete`.
/--
info: iykyk
  root: source
  witnesses: (none)
  facts:
    [0] P1 source
    [1] P2 source
    [2] P3 source
    [3] P4 source
    [4] P5 source
    [5] P6 source
    [6] P7 source
  certificate: P1 source ∧ P2 source ∧ P3 source ∧ P4 source ∧ P5 source ∧ P6 source ∧ P7 source
  status: complete
-/
#guard_msgs in
example (source : Vertex) (P1 P2 P3 P4 P5 P6 P7 : Vertex → Prop)
    (seed : P1 source)
    (r1 : ∀ x, P1 x → P2 x) (r2 : ∀ x, P2 x → P3 x) (r3 : ∀ x, P3 x → P4 x)
    (r4 : ∀ x, P4 x → P5 x) (r5 : ∀ x, P5 x → P6 x) (r6 : ∀ x, P6 x → P7 x) : True := by
  iykyk source using [r1, r2, r3, r4, r5, r6]
  trivial

-- A genuinely productive rule never reaches a fixpoint, so it must still report `truncated`.
/--
info: iykyk
  root: start
  witnesses: (none)
  facts:
    [0] Reach start
    [1] Reach (next start)
    [2] Reach (next (next start))
    [3] Reach (next (next (next start)))
    [4] Reach (next (next (next (next start))))
    [5] Reach (next (next (next (next (next start)))))
    [6] Reach (next (next (next (next (next (next start))))))
    [7] Reach (next (next (next (next (next (next (next start)))))))
    [8] Reach (next (next (next (next (next (next (next (next start))))))))
  certificate: Reach start ∧
  Reach (next start) ∧
    Reach (next (next start)) ∧
      Reach (next (next (next start))) ∧
        Reach (next (next (next (next start)))) ∧
          Reach (next (next (next (next (next start))))) ∧
            Reach (next (next (next (next (next (next start)))))) ∧
              Reach (next (next (next (next (next (next (next start))))))) ∧
                Reach (next (next (next (next (next (next (next (next start))))))))
  status: truncated
-/
#guard_msgs in
example (start : Vertex) (next : Vertex → Vertex)
    (seed : Reach start) (step : ∀ x, Reach x → Reach (next x)) : True := by
  iykyk start using [step]
  trivial

example (start : Vertex) (positive : Reach start) (negative : ¬ Reach start) : True := by
  iykyk start
  trivial

end Iykyk.Examples.Bounded
