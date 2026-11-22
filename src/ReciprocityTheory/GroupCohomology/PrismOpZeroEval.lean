import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.ContinuousContractNth
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB

namespace ReciprocityTheory.Coh

open Function

universe u

section Comb

variable {V X Y : Type u} [AddCommGroup V]

theorem hd_comp' (n : ℕ) (F : (Fin (n + 1) → Y) → V) (c : X → Y) (x : Fin (n + 2) → X) :
    hd n (fun y => F fun i => c (y i)) x = hd n F (fun i => c (x i)) := rfl

theorem prismOp_zero (a b : X → Y) (F : (Fin 2 → Y) → V) (x : Fin 1 → X) :
    prismOp a b 0 F x = F (Fin.cons (a (x 0)) fun j => b (x j)) := rfl

theorem prismOp_succ (a b : X → Y) (n : ℕ) (F : (Fin (n + 3) → Y) → V) (x : Fin (n + 2) → X) :
    prismOp a b (n + 1) F x = F (Fin.cons (a (x 0)) fun j => b (x j)) -
      prismOp a b n (fun y => F (Fin.cons (a (x 0)) y)) (Fin.tail x) := rfl

end Comb

end ReciprocityTheory.Coh
