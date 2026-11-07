import Definitions.Def_Schwichtenberg1976_Lambda

namespace ExtendedPolynomialAudit
open Schwichtenberg1976

def x : Var := ⟨2, .zero⟩
def y : Var := ⟨3, .zero⟩
def constantX : Term := .lam y (.var x)
def identity : Term := .lam y (.var y)

theorem inputs_typed : HasType constantX Ty.endo ∧ HasType identity Ty.endo := by
  exact ⟨.lam y (.var x), .lam y (.var y)⟩

theorem constant_has_free_x : freeVars constantX = [x] := by decide

-- The default binder 2 captures the input's free x : 0.
theorem default_composition_captures :
    freeVars (compTerm .zero constantX identity) = [] := by decide

-- The very same inputs retain their free x when a genuinely fresh binder is used.
theorem fresh_composition_preserves :
    freeVars (compTerm .zero constantX identity 4) = [x] := by decide

def zeroVar : Var := ⟨0, .zero⟩
def constantZeroVar : Term := .lam y (.var zeroVar)

theorem iteration_captures :
    freeVars constantZeroVar = [zeroVar] ∧
    freeVars (iterTerm constantZeroVar 0 1) = [] ∧
    freeVars (iterTerm constantZeroVar 4 1) = [zeroVar] := by decide

-- These are defects in the general-purpose helpers, not disproofs of the
-- four submitted theorem targets: their explicit combinator calls avoid capture.
#print axioms inputs_typed
#print axioms constant_has_free_x
#print axioms default_composition_captures
#print axioms fresh_composition_preserves
#print axioms iteration_captures
end ExtendedPolynomialAudit
