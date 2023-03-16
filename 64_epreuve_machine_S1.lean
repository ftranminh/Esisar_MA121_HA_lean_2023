import data.nat.basic
import data.set.basic
import data.real.basic


-- ------------------ EXERCICE 1 ------------------

namespace ex1

theorem ex_1_1 : ∀ P:Prop, P → P := assume P:Prop, assume h:P, show P, from h

theorem ex_1_2 : ∀ P Q:Prop, P ∧ Q → P ∨ Q := assume P Q:Prop, assume h:P ∧ Q, show P ∨ Q, from or.inl h.left

end ex1

-- ------------------ EXERCICE 2 ------------------

namespace ex2

variables {E F G:Type}

definition injective  (f: E → F) : Prop  := ∀ (u:E), ∀ (v:E), f u=f v → u=v

theorem ex_2_1 : ∀ f:E→ F, ∀ g:F→ G, (injective f) ∧ (injective g) → (injective (g ∘ f)) :=
   assume f:E→ F,
     assume g:F→ G,
       assume h1:(injective f) ∧ (injective g),
         assume u v :E,
           assume h2: (g ∘ f) u =(g ∘ f) v,
             have h3 : f u=f v, from h1.right (f u) (f v) h2,
             show u = v, from h1.left u v h3


theorem ex_2_2 : ∀ f:E→ F, ∀ g:F→ G,  injective (g ∘ f) → injective f :=
   assume f:E→ F,
     assume g:F→ G,
       assume h1:injective (g ∘ f),
         assume u v :E,
           assume h2: f u =f v,
             have h3:g (f u) =g (f v), from congr_arg g h2,
             show u=v, from h1 u v h3

end ex2
-- ------------------ EXERCICE 3 ------------------

namespace ex3

definition divisible (n p:ℕ) := ∃k:ℕ , n=k*p

theorem  ex_3_2 : ∀ p m n :ℕ , (divisible m p)∧ (divisible n p) → (divisible (m+n) p) :=
   assume p m n : ℕ, 
      assume h: (divisible m p)∧ (divisible n p),
        exists.elim h.left (
          assume (j:ℕ )  (h_m: m = j*p),
          exists.elim h.right (
            assume (k:ℕ ) (h_n : n = k*p),
              exists.intro (j+k) (
                calc
                  m+n = j*p+n      : h_m ▸ (eq.refl (m+n))      -- congr_arg (λ z, z+n)   h_m  --
                  ... = j*p+k*p    : h_n ▸ (eq.refl (j*p+n))    -- congr_arg (λ z, j*p+z) h_n  --
                  ... = (j+k)*p    : (right_distrib j k p).symm
              )
          )
        )
 
end ex3

-- ------------------ EXERCICE 4 ------------------

namespace ex4

definition est_majorant (A:set ℝ) (m:ℝ)  : Prop := ∀ x:ℝ , x ∈ A → x ≤ m  
definition est_majorant' (A:set ℝ) (m:ℝ) : Prop := ∀ x∈ A, x ≤ m  
#print  est_majorant'

definition est_pge  (A:set ℝ) (m:ℝ) : Prop := m∈A ∧ (est_majorant A m)

theorem ex_4_3 : ∀ (A:set ℝ) (m:ℝ ) (n:ℝ ), (est_pge A m) ∧ (est_pge A n)→ m=n :=
  assume  (A:set ℝ) (m:ℝ ) (n:ℝ ),
    assume (h1: (est_pge A m) ∧ (est_pge A n)),
      have h2 : m ≤ n, from h1.right.right m h1.left.left,
      have h3 : n ≤ m, from h1.left.right n h1.right.left, 
      show m=n, from le_antisymm h2 h3

end ex4

-- ------------------ QCM Open ------------------
 
namespace qcm_open

  variables {E F G:Type}

  definition injective  (f: E → F) : Prop  := ∀ (u:E), ∀ (v:E), f u = f v  →  u = v
  definition surjective (f: E → F) : Prop  := ∀ (y:F), ∃ (x:E), y = f x

  theorem interessant : ∀  (u: E → F) (v: F → G), surjective (v ∘ u) → (injective v) → (surjective u) := 
  assume  (u: E → F) (v: F → G),
    assume h1 : surjective (v ∘ u),
      assume h2: injective v,
        assume (y:F),
          let z:= v y in
           exists.elim (h1 (z:G))
           (
             assume (x:E) (h3: z = (v ∘ u) x),
             have h4: v y = v (u x), from h3,
             exists.intro x (
               show y = u x, from h2 y (u x) h4
             )
           )
/-
  Soient E, F, G trois ensembles.

  Définition :  Soit f une application de E dans F. On dit que f est injective si et seulement si pour tous u et v dans E, 
  tels que f(u) = f(v), on a u=v.

  Définition :  Soit f une application de E dans F. On dit que f est surjective si et seulement si pour tout y dans F, 
  il existe x dans E tel que y=f(x).

  Théorème : Pour toutes applications u de E dans F et v de F dans F, 
  si v o u est surjective et v est injective alors u est surjective.

  Preuve : Soient u une application de E dans F et v une application de F dans G. 
  On suppose que v o u est surjective, et que v est injective. 
  Soit y appartenant à F. (pour satisfaire la définition de surjectivité de u, on cherche x dans E tel que y=u(x))
  On pose z:= v(y). 
  En appliquant la surjectivité de v o u  à z, qui est bien un élément de G, on obtient l'existence
  d'un élément x de E tel que z = (v o u) (x).  Ainsi, on a v(y) = v(u(x)).
  Mais alors ce x convient, puisque l'injectivité de v donne y=u(x).

-/
end qcm_open