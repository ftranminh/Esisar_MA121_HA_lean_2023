import data.nat.basic
import data.real.basic
import data.set

-- §3 : séance 1 : premiers pas ; quantificateur universel et implication
-- §3.1 : Pas à pas : un premier théorème

namespace sec31 

  -- Ceci est un commentaire: ce texte est ignoré par le compilateur
  theorem mon_premier_theoreme :    -- nom du théorème : énoncé du théorème := preuve du théorème
      ∀ P:Prop, P → P:=            -- Le symbole ∀ s’obtient en tapant \all puis espace 

  assume (P:Prop),                  -- Le symbole → s’obtient en tapant \r puis espace
    assume(h1 : P),                 -- Voir l’annexe pour tous les raccourcis
      show P, from h1       


  theorem mon_premier_theoreme' : ∀ P:Prop, P → P :=
    assume (P:Prop),
    (
      assume(h1 : P),
      (
        show P, from h1
      )
    )

  theorem mon_premier_theoreme'' : ∀ P:Prop, P → P  :=  sorry

end sec31

-- §3.3 : Introduction / élimination du quantificateur universel


namespace sec33

  namespace regles
    constant E:Type
    constant P:E → Prop

    theorem Assertion1: ( ∀ x:E ,P x) :=
      assume(x: E),
        show P x, from sorry

    example (y:E) : P y  := Assertion1 y
  end regles 

  namespace exemple
    theorem Assertion1: ( ∀ x: ℝ  ,x^2 ≥  0) :=
      assume(x: ℝ  ),
        show (x^2 ≥  0), from sq_nonneg x

    example (y: ℝ  ) : y^2-2*y+1 ≥  0 := 
      calc
        y^2-2*y+1 = (y-1)^2 : by ring
        ...       ≥ 0 : Assertion1 (y-1)     -- élimination: on applique Assertion1 au réel (y-1)

  end exemple
end sec33

-- § 3.4 : Introduction / élimination de l’implication
namespace sec34

  namespace regles
    constants P Q : Prop

    theorem Assertion2: ( P → Q) := 
      assume (h1: P),
        show Q, from sorry

  end regles

  theorem ex_3_4_1 : ∀ P Q : Prop, P → (Q → P) := 
    assume P Q: Prop,
      assume h_P : P,
        assume h_Q : Q, 
          show P, from h_P

  theorem ex_3_4_1' : ∀ P Q : Prop, P → (Q → P) := 
    λ  _ _ hP _, hP
  
end sec34

-- § 4 : séance 2 : les connecteurs logiques ( ∧ , ∨ , ¬, ↔) et le quantificateur existentiel (∃)

-- §4.1 : La conjonction ( ∧ , ET)

namespace sec41
  namespace regles
    constants P Q : Prop
    constants (h1 : P) (h2:Q)

    theorem Assertion1: P ∧ Q := 
      and.intro h1 h2

    example : P := Assertion1.left
    example : Q := Assertion1.right
    
  end regles


  namespace exemples
    theorem T2 : ∀ P Q:Prop, P → (Q → P ∧ Q) :=
      assume (P Q:Prop),
      (
        assume(h1 : P),
        (
          assume(h2 : Q),
          (
            (and.intro h1 h2): P ∧ Q
          )
        )
      )

    theorem T2' : ∀ P Q:Prop, P → (Q → P ∧ Q) :=
      λ _ _ h1 h2, ⟨ h1,h2 ⟩  


    theorem T3 : ∀ P Q : Prop, P ∧ Q → P :=
      assume (P Q :Prop) ,
      (
        assume (h: P ∧ Q),
        (
          show P, from h.left
        )
      )      

    theorem T3' : ∀ P Q : Prop, P ∧ Q → P :=
      λ _ _ h, h.1

  end exemples

  namespace exercices
    theorem ex_4_1_2_1 : ∀ P Q : Prop, P ∧ Q → Q := 
      assume (P Q :Prop) ,
      (
        assume (h: P ∧ Q),
        (
          show Q, from h.right
        )
      )      

    theorem ex_4_1_2_1' : ∀ P Q : Prop, P ∧ Q → Q :=
      λ _ _ h, h.2

    theorem ex_4_1_2_3 : ∀ P Q : Prop, P ∧ Q → Q ∧ P :=   
      assume (P Q :Prop) ,
      (
        assume (h: P ∧ Q),
        (
          show Q ∧ P, from and.intro h.right h.left 
        )
      )      

    theorem ex_4_1_2_3' : ∀ P Q : Prop, P ∧ Q → Q ∧ P :=   
      λ _ _ h, ⟨ h.2, h.1 ⟩ 



  end exercices
end sec41



-- § 4.2 : La disjonction ( ∨ , OU)


namespace sec42
  namespace regles
    constants P Q R : Prop

    constant h1 : P
    theorem Assertion1: P ∨ Q := 
      or.inl h1 

    constant h2:Q
    theorem Assertion1': P ∨ Q := 
      or.inr h2 

    example : R := 
      or.elim Assertion1
      (
        assume (h1:P), (sorry:R)
      )
      (
        assume (h2:Q), (sorry:R)
      )
    
  end regles


  namespace exemples
    theorem T4 : ∀ P Q : Prop, P → P ∨ Q :=
      assume (P Q :Prop) ,
      (
        assume (h: P),
        (
          show  P ∨ Q, from  or.inl h
        )
      )

    theorem T4' : ∀ P Q : Prop, P → P ∨ Q :=
      λ _ _ hP, or.inl hP

  end exemples

  namespace exercices
    theorem ex_4_2_3 : ∀ P Q : Prop, P ∧ Q → P ∨ Q :=
      assume (P Q :Prop) ,
      (
        assume (h: P ∧ Q),
        (
          show  P ∨ Q, from  or.inl h.left
        )
      )
      
    theorem ex_4_2_3' : ∀ P Q : Prop, P ∧ Q → P ∨ Q :=
      assume (P Q :Prop) ,
      (
        assume (h: P ∧ Q),
        (
          show  P ∨ Q, from  or.inr h.right
        )
      )
      
    theorem ex_4_2_3'' : ∀ P Q : Prop, P ∧ Q → P ∨ Q :=
      λ _ _ h, or.inl h.1

    theorem ex_4_2_3''' : ∀ P Q : Prop, P ∧ Q → P ∨ Q :=
      λ _ _ h, or.inr h.2
      
  end exercices
end sec42

-- §4.3 : La négation

namespace sec43
  namespace regles
    constants P : Prop

    theorem Assertion1: ¬ P := 
      assume (h1:P),
        show false, from sorry

    constant LesPoulesOntDesDents : Prop
    constant Assertion2: P
    example : LesPoulesOntDesDents :=
      absurd Assertion2 Assertion1
  end regles

  namespace exercices

    constants IlFaitBeau IlPleut JeprendsMonParapluie : Prop
    axiom a1: IlFaitBeau ∨ IlPleut
    axiom a2: IlPleut → JeprendsMonParapluie


    theorem ex_4_3_4 : ¬ IlFaitBeau → JeprendsMonParapluie := 
      assume (h_il_fait_moche: ¬ IlFaitBeau),
       or.elim a1   -- disjonction de cas
       (            -- 1er cas : IlFaitBeau
          assume h_1er_cas_il_fait_beau:IlFaitBeau,
            absurd h_1er_cas_il_fait_beau h_il_fait_moche
       )
       (            -- 2e cas : IlPleut
          assume h_2e_cas_il_pleut:IlPleut,
            show JeprendsMonParapluie, from a2 h_2e_cas_il_pleut
       )

    theorem ex_4_3_4' : ¬ IlFaitBeau → JeprendsMonParapluie := 
      λ h, or.elim a1 (λ h1,  absurd h1 h) (λ h2, a2 h2)

  end exercices
end sec43


-- § 4.4 : L'équivalence

namespace sec44
  namespace regles
    constants P Q : Prop

    constant h1: P → Q
    constant h2: Q → P
    theorem Assertion1 : P ↔ Q  :=
      iff.intro h1 h2

    theorem Assertion1' : P ↔ Q  :=
      iff.intro
      (
        assume (h_P: P) ,
          show Q, from sorry
      )
      (
        assume (h_Q: Q) ,
          show P, from sorry
      )
    

    example : P → Q := Assertion1.mp
    example : Q → P := Assertion1.mpr

  end regles

  namespace exercices
     theorem ex_4_4_5_1 : ∀ P Q : Prop, P ∧ Q ↔ Q ∧ P :=
      assume P Q : Prop,
        iff.intro
        (
          assume h_P_and_Q: P ∧ Q,
            show Q ∧ P, from and.intro h_P_and_Q.right h_P_and_Q.left
        )
        (
          assume h_Q_and_P: Q ∧ P,
            show P ∧ Q, from and.intro h_Q_and_P.right h_Q_and_P.left
        )

     theorem ex_4_4_5_1' : ∀ P Q : Prop, P ∧ Q ↔ Q ∧ P :=
      assume P Q : Prop,
         iff.intro 
            (sec41.exercices.ex_4_1_2_3 P Q)
            (sec41.exercices.ex_4_1_2_3 Q P)

     theorem ex_4_4_5_1'' : ∀ P Q : Prop, P ∧ Q ↔ Q ∧ P :=
      λ  _ _, ⟨ λ h, ⟨ h.2, h.1 ⟩ , λ h, ⟨ h.2, h.1 ⟩ ⟩ 

     theorem ex_4_4_5_3 : ∀ P Q : Prop, P ∨ Q ↔ Q ∨ P :=
      assume P Q : Prop,
        iff.intro
        (
          assume h_P_or_Q: P ∨ Q,
            or.elim h_P_or_Q
            (
              assume h_P:P, show Q ∨ P, from or.inr h_P
            )
            (
              assume h_Q:Q, show Q ∨ P, from or.inl h_Q
            )
        )
        (
          assume h_Q_or_P: Q ∨ P,
            or.elim h_Q_or_P
            (
              assume h_Q:Q, show P ∨ Q, from or.inr h_Q
            )
            (
              assume h_P:P, show P ∨ Q, from or.inl h_P
            )
        )

     theorem ex_4_4_5_3' : ∀ P Q : Prop, P ∨ Q ↔ Q ∨ P :=
      λ  _ _, ⟨ λ h, or.elim h (λ hP, or.inr hP) (λ hQ, or.inl hQ),
                λ h, or.elim h (λ hQ, or.inr hQ) (λ hP, or.inl hP) ⟩ 

     lemma L1 : ∀ P Q : Prop, P ∨ Q →  Q ∨ P :=
       λ  _ _,  λ h, or.elim h (λ hP, or.inr hP) (λ hQ, or.inl hQ)

     theorem ex_4_4_5_3'' : ∀ P Q : Prop, P ∨ Q ↔ Q ∨ P :=
      λ  _ _, ⟨ L1 _ _, L1 _ _⟩ 


      theorem ex_4_4_6 : ∀ (A B:Prop), (A ∨ B) ↔ ((A → B) → B) := 
        assume A B : Prop,
          iff.intro
          (
            assume h_A_or_B : A ∨ B ,
              assume h_A_imp_B : A → B, 
                or.elim h_A_or_B 
                (
                  assume h_A :A, 
                    show B, from h_A_imp_B h_A
                )
                (
                  assume h_B :B, 
                    show B, from h_B
                )
          )
          (
            assume h_A_imp_B_imp_B : (A → B) → B,
              have h_A_or_not_A : A ∨ ¬ A, from classical.em A,
              or.elim h_A_or_not_A
              (
                assume h_A : A,
                 show  A ∨ B, from or.inl h_A
              )
              (
                assume h_not_A : ¬ A,
                  have h_A_imp_B :  A → B, from 
                    assume h_A : A,
                    show B, from absurd h_A h_not_A,
                  
                  have h_B : B, from
                    h_A_imp_B_imp_B h_A_imp_B,

                  show  A ∨ B, from or.inr h_B
              )
          )

      theorem ex_4_4_6' : ∀ (A B:Prop), (A ∨ B) ↔ ((A → B) → B) := 
        λ _ _, ⟨ λ h1 h2, or.elim h1 h2 id ,
                 λ h3, or.elim (classical.em _)  or.inl (or.inr ∘ h3 ∘ not.elim)  ⟩ 


      theorem ex_4_4_7_squelette : ∀ a:ℝ, ∀ b:ℝ, ( (∀ x:ℝ, a*x + b =0   ) ↔ (a=0 ∧ b=0) ) := 
        assume (a:ℝ) (b:ℝ) , iff.intro
          (assume h: ∀ x:ℝ, a*x + b =0 , 

            have e1 : a*1+b=0 , from  h 1 ,
            have e2 : a*0+b=0 , from  h 0 ,

            have e3 : a+b=0,    from sorry,
            have e4 : b=0,      from sorry,
            have e5 : a=0,      from sorry,
            and.intro e5 e4
          )
          (assume hab : a=0 ∧ b=0, 
            assume x:ℝ ,
              show a*x+ b = 0 , from sorry
          )
    
      theorem ex_4_4_7_complete : ∀ a:ℝ, ∀ b:ℝ, ( (∀ x:ℝ, a*x + b =0   ) ↔ (a=0 ∧ b=0) ) := 
        assume (a:ℝ) (b:ℝ) , iff.intro
          (assume h: ∀ x:ℝ, a*x + b =0 , 
            have e1 : a*1+b=0 , from  h 1 ,
            have e2 : a*0+b=0 , from  h 0 ,

            have e3 : a+b=0,    from 
              calc 
                a+b = a*1+b : (congr_arg (λ z:ℝ , z+b) (mul_one a)).symm
                ... = 0     : e1
                ,

            have e4 : b=0,      from 
                calc
                  b   = 0 + b   : (zero_add b).symm
                  ...  = a*0 + b : congr_arg (λ z:ℝ, z+b) (mul_zero a).symm 
                  ...  = 0       : e2
                ,

            have e5 : a=0,      from   
                calc
                  a   = a+0  : (add_zero a).symm
                  ... = a+b  : congr_arg  (λ z:ℝ, a+z) e4.symm
                  ... = 0    : e3
                ,
            and.intro e5 e4
          )
          (assume hab : a=0 ∧ b=0, 
            assume x:ℝ ,
              calc 
                a*x+ b = a*x+0 : congr_arg (λ z:ℝ, a*x+z) hab.right 
                  ...  = 0*x+0 : congr_arg (λ z:ℝ, z*x+0) hab.left  
                  ...  = 0*x   : add_zero (0*x)
                  ...  = 0     : zero_mul x
          )
    
      theorem ex_4_4_7_complete' : ∀ a:ℝ, ∀ b:ℝ, ( (∀ x:ℝ, a*x + b =0   ) ↔ (a=0 ∧ b=0) ) := 
        assume (a:ℝ) (b:ℝ) , iff.intro
          (assume h: ∀ x:ℝ, a*x + b =0 , 
            have e1 : a*1+b=0 , from  h 1 ,
            have e2 : a*0+b=0 , from  h 0 ,

            have e3 : a+b=0,    from 
              calc 
                a+b = a*1+b :  (mul_one a).symm ▸ eq.refl (a+b)
                ... = 0     : e1
                ,

            have e4 : b=0,      from 
                calc
                  b   = 0 + b   : (zero_add b).symm
                  ...  = a*0 + b : (mul_zero a).symm ▸ eq.refl (0+b)
                  ...  = 0       : e2
                ,

            have e5 : a=0,      from   
                calc
                  a   = a+0  : (add_zero a).symm
                  ... = a+b  :  e4.symm ▸ eq.refl (a+0)
                  ... = 0    : e3
                ,
            and.intro e5 e4
          )
          (assume hab : a=0 ∧ b=0, 
            assume x:ℝ ,
              calc 
                a*x+ b = a*x+0 : hab.right ▸ eq.refl (a*x+b)
--                  ...  = 0*x+0 : @eq.subst ℝ  (λ z, a*x+0 = z*x+0 ) a 0 hab.left   (eq.refl (a*x+0))  -- hab.left ▸ eq.refl (a*x+0)
                  ...  = 0*x+0 : @eq.subst _  (λ z, a*x+0 = z*x+0 ) _ _ hab.left   (eq.refl _)  -- hab.left ▸ eq.refl (a*x+0)
                  ...  = 0*x   : add_zero (0*x)
                  ...  = 0     : zero_mul x
          )

      theorem ex_4_4_7' : ∀ a:ℝ, ∀ b:ℝ, ( (∀ x:ℝ, a*x + b =0   ) ↔ (a=0 ∧ b=0) ) := 
        λ a b ,⟨ 
          (λ h,   and.intro (by linarith[h 0, h 1] )  (by linarith[h 0]) ) ,
          (λ z x, by simp[z.left,z.right] )  ⟩ 

      #check @mt
      #check @not_not

      theorem ex_4_4_8 : ∀ P Q : Prop, (P ↔ Q) ↔ ((P → Q) ∧ ( ¬ P →¬ Q)) :=
         assume P Q : Prop,
           iff.intro
             (
               assume h_P_eqv_Q: P ↔ Q,
                 and.intro h_P_eqv_Q.mp (mt h_P_eqv_Q.mpr)
             ) 
             (
               assume h_2_imps : (P → Q) ∧ ( ¬ P →¬ Q),
                 iff.intro 
                   h_2_imps.left 
                   (assume hQ:Q,
                     show P, from not_not.mp (assume hnP:¬ P,
                        have hnQ : ¬ Q, from h_2_imps.right hnP,
                        show false, from absurd hQ hnQ
                     )
                   )
             )

      theorem ex_4_4_8' : ∀ P Q : Prop, (P ↔ Q) ↔ ((P → Q) ∧ ( ¬ P →¬ Q)) :=
         λ P Q,  ⟨ λ h, ⟨ h.mp,  (mt h.mpr) ⟩  , 
                   λ h, ⟨ h.1,   (λ  hQ, not_not.mp (λ  hnP,  absurd hQ (h.2 hnP) ))  ⟩   ⟩ 

  end exercices
end sec44

-- § 4.5 : Quantificateur existentiel

namespace sec45

  namespace regles
     constant E: Type
     constant P: E → Prop

     constant a:E
     constant ha: P a
     theorem Assertion1 : ∃ x:E, P x := exists.intro a ha

     constant R:Prop
     example : R := exists.elim Assertion1 (
        assume (x:E),
          assume (hPx : P x),
            (sorry:R)
     )
  end regles

  namespace exemples

    #check mul_assoc

    definition entier_pair (n:ℕ  ) : Prop := ∃ (k:ℕ  ), n = 2*k

    theorem multiple_de_4_pair : ∀ k:ℕ  , entier_pair (4*k) :=
      assume (k: ℕ ),
      (
        exists.intro
        (2*k)
        (calc
            4*k = (2*2)*k : eq.refl _
            ... = 2*(2*k) : mul_assoc 2 2 k
        )
      )  
  end exemples

  namespace exercices
  end exercices

end sec45

-- §5 : séance 3 : quelques premières vraies preuves de maths : entiers naturels, fonctions, calculs

-- §5.1 : Faire des calculs avec L ∃∀N : have , calc , congr_arg

namespace sec51
  namespace exemples

    -- la ligne ci-dessous définit la fonction f qui à un réel x associe x+1
    definition f := λ x:ℝ  , x+1

    -- de façon équivalente, voici la fonction g (égale  à f )
    definition g : ℝ → ℝ := λ x, x+1


    -- congr_arg
    constants u v w : ℝ 
    constant h_uv : u=v
    constant h_vw : v=w
    #check congr_arg f h_uv
    #check h_uv.symm
    #check eq.symm h_uv
    #check eq.trans h_uv h_vw
    #check eq.refl u

    example : 2*2 = 4 := eq.refl 4

    #check sub_self
    #check @sub_self
    #check add_sub
    #check @add_sub


    theorem T : ∀ a:ℝ,   a+1=1 → ∀ x:ℝ, a*x = 0 := 
      assume a:ℝ, 
        assume hyp1 : a+1=1,
          assume x:ℝ, 

            have hyp2 : (1:ℝ) -1 = 0, from sub_self 1,
            have hyp3 : a=0, from 
              calc 
                a   = a+ 0        : (add_zero a).symm
                ... = a+(1-1)     : congr_arg (λ z:ℝ, a+z) hyp2.symm
                ... = a+1 - 1     : add_sub a 1 1
                ... = 1 -1        : congr_arg (λ z:ℝ , z-1) hyp1
                ... = 0           : hyp2
              , 
            calc 
              a*x = 0*x : congr_arg (λ z:ℝ , z*x) hyp3
              ... = 0   : zero_mul x
  end exemples

  namespace exercices

    #check zero_add
    #check add_zero
    #check zero_mul
    #check mul_zero
    #check mul_one

    theorem ex_5_1_9_1 : ∀ a: ℝ  , ∀ b: ℝ  , ((a=0 ∧ b=0) → ( ∀ x: ℝ  , a*x + b =0)) := 
       assume a b : ℝ, (sec44.exercices.ex_4_4_7_complete a b).mpr

    theorem ex_5_1_9_2 : ∀ a: ℝ  , ∀ b: ℝ  , ( ∀ x: ℝ  , a*x + b =0) ↔ (a=0 ∧ b=0) := 
       sec44.exercices.ex_4_4_7_complete

  end exercices
end sec51

-- §5.2 : Avec des entiers : nombres pairs, nombres impairs

namespace sec52

  namespace exercices
    #check mul_add
    definition entier_pair (n:ℕ  ) : Prop := ∃ (k:ℕ  ), n = 2*k
    definition entier_impair (n:ℕ  ) : Prop := ∃ (k:ℕ  ), n = 2*k+1
    
    theorem sum_entiers: ∀ m n :ℕ, (entier_pair m) ∧ (entier_pair n) → (entier_pair (m+n)) :=
      assume (m n :ℕ ),
        assume h_m_n_pairs :   (entier_pair m) ∧ (entier_pair n),
          exists.elim  h_m_n_pairs.left (
            assume j:ℕ , assume h_m_2j: m=2*j,
              exists.elim  h_m_n_pairs.right (
                assume k:ℕ , assume h_n_2k: n=2*k,
                  exists.intro (j+k) (
                    calc 
                      m+n = 2*j+n   : congr_arg ( λ z, z+n)   h_m_2j
                      ... = 2*j+2*k : congr_arg ( λ z, 2*j+z) h_n_2k
                      ... = 2*(j+k) : (mul_add 2 j k).symm
                  )
              )
          )

    theorem sum_entiers': ∀ m n :ℕ, (entier_pair m) ∧ (entier_pair n) → (entier_pair (m+n)) :=
      assume (m n :ℕ ),
        assume h_m_n_pairs :   (entier_pair m) ∧ (entier_pair n),
          exists.elim  h_m_n_pairs.left (
            assume j:ℕ , assume h_m_2j: m=2*j,
              exists.elim  h_m_n_pairs.right (
                assume k:ℕ , assume h_n_2k: n=2*k,
                  exists.intro (j+k) (
                    calc 
                      m+n = 2*j+n   : h_m_2j ▸ eq.refl (m+n)
                      ... = 2*j+2*k : h_n_2k ▸ eq.refl (2*j+n)
                      ... = 2*(j+k) : (mul_add 2 j k).symm
                  )
              )
          )

    theorem sum_entiers'': ∀ m n :ℕ, (entier_pair m) ∧ (entier_pair n) → (entier_pair (m+n)) := 
      λ _ _  ⟨ ⟨ j, _⟩ , ⟨k, _ ⟩ ⟩ , ⟨  (j+k) ,by linarith ⟩ 


  end exercices
end sec52 

  -- §5.3 : Avec des fonctions

namespace sec53
  namespace exercices

    definition fonction : Type := ℝ → ℝ 
    definition croissante (f:fonction) := ∀x:ℝ , ∀ y:ℝ , x ≤ y → (f x) ≤ (f y)



    theorem compo_croissantes : ∀ (f g : fonction), (croissante f) → (croissante g) → (croissante (f ∘ g)) :=    
      assume (f g : fonction),
        assume (hcf:croissante f)(hcg:croissante g), 
          assume (x:ℝ ) (y:ℝ), 
            assume  (hxy: x ≤ y), 
            have  h_gx_gy : g x ≤ g y,          from hcg x y hxy,
            show            f (g x) ≤ f (g y),  from hcf (g x) (g y) h_gx_gy

    theorem compo_croissantes' {f g : fonction} : (croissante f) → (croissante g) → (croissante (f ∘ g)) :=    
      λ  hcf hcg x y hxy, hcf (g x) (g y) (hcg x y hxy)



    definition somme_fonctions (f:fonction) (g:fonction):= (λ x:ℝ , f x + g x)
     -- infix `+` 50 := somme_fonctions
    instance fonction_has_add : has_add fonction :=⟨somme_fonctions⟩
 
    #check add_le_add

    theorem sum_croissantes : ∀ (f g : fonction),  (croissante f) → (croissante g) → (croissante (f+g)) :=    
      assume (f g : fonction),
        assume (hcf:croissante f)(hcg:croissante g),        -- Soient f et g deux fonctions croissantes
          assume (x:ℝ ) (y:ℝ) (hxy: x ≤ y),                 -- On se donne deux réels x et y tels que x ≤ y
          calc  
              (f+g) x = (f x) + (g x)  : eq.refl _            -- Alors ...
                ...    ≤ (f y) + (g y) : add_le_add (hcf x y hxy) (hcg x y hxy) 
                ...    = (f+g) y       : eq.refl _


    theorem sum_croissantes': ∀ (f g : fonction), (croissante f) → (croissante g) → (croissante (f+g)) :=    
      assume (f g : fonction),
        assume (hcf:croissante f)(hcg:croissante g), 
          assume (x:ℝ ) (y:ℝ) (hxy: x ≤ y),              
          show   (f+g) x ≤ (f+g) y, from add_le_add (hcf x y hxy) (hcg x y hxy)  

    theorem sum_croissantes'' {f g : fonction} : (croissante f) → (croissante g) → (croissante (f+g)) :=    
      λ  hcf hcg x y hxy, add_le_add (hcf x y hxy) (hcg x y hxy)  

    theorem sum_croissantes''' {f g : fonction} : (croissante f) → (croissante g) → (croissante (f+g)) :=    
      λ  hcf hcg x y hxy, by simp [hcf x y hxy, hcg x y hxy,add_le_add]



  end exercices
end sec53


-- §6 : séance 4 : applications

namespace sec6
  --29.lean, 35.lean, 47.lean, 12.lean, 57.lean, 59.lean


  -- intro : set  ; notation {} ; distinction avec types

  -- les symboles introduits par variables seront des arguments à toutes les fonctions / théorèmes / définitions qui vont suivre
  -- Les accolades au lieu des parenthèses désignent des arguments implicites (à l'utilisation Lean essaye de les deviner)

  -- Ici on va se donner trois types E , F  et G pour toute cette partie :


  variables {E F G : Type}

  -- § 6.1 : Injectivité, surjectivié

  -- exercice 6.1.12 
  -- Donnez les définitions d'application injective, surjective, bijective
  -- Utilisez le mot clé  definition
  definition injective  (f: E → F) : Prop  := ∀ (u:E), ∀ (v:E), ( f u = f v → u = v )
  definition surjective (f: E → F) : Prop  := ∀ (y:F), ∃ (x:E), y= f x
  definition bijective  (f: E → F) : Prop  := (injective f) ∧ (surjective f)

  -- exercice 6.1.13
  -- Définissez l'application identité de E, puis montrez qu'elle est injective, surjective, bijective
  -- On rappelle que la flèche à talons des maths ( x:E \mapsto y) se note (λ x:E, y)

  definition identite : E → E := λ x:E, x 
  theorem identite_injective  : @injective E E identite  := 
    assume u:E,
        assume v:E,
          assume h:identite u = identite v,
            show u=v, from h


  theorem identite_surjective : @surjective E E identite  := 
    assume (y:E), 
      exists.intro y (
        show y = identite y, from eq.refl y
      )
      
  theorem identite_bijective : @bijective E E identite := and.intro identite_injective identite_surjective

  -- exercice 6.1.14
  -- Montrez que la composée de deux applications injectives est injective
  -- Idem pour surjectives, bijectives

  theorem composee_injections : ∀ (f: E → F ), ∀  (g : F → G ), ((injective   f)∧ (injective  g)) → (injective (g ∘ f)) := 
    assume (f:E → F ),
      assume (g:F → G ),
        assume (h1: (injective f)∧ (injective  g)),
            assume (u v : E ),
              assume (h2 : (g ∘ f) u = (g ∘ f) v),
                have h3 : f u = f v, from  h1.right (f u) (f v) h2,
                show        u = v  , from  h1.left   u     v    h3


  theorem composee_surjections : ∀ (f: E → F ), ∀  (g : F → G ), ((surjective f)∧ (surjective g)) → (surjective (g ∘ f)) := 
    assume (f:E → F ),
      assume (g:F → G ),
        assume (h1: (surjective  f)∧ (surjective   g)),
            assume (z : G  ),
              have  h2: (∃ y:F , z = g y), from h1.right z ,
              exists.elim h2 (
                assume (y:F ), assume (h3: z = g y),
                  have h4: ∃ x:E , y = f x, from h1.left y,
                  exists.elim h4 (
                    assume (x:E ) , assume (h5: y = f x),
                      exists.intro x (
                          calc 
                            z   = g y     : h3
                            ... = g (f x) : congr_arg g h5
                        )
                  )
              )

  theorem composee_bijections  : ∀ (f: E → F ), ∀  (g : F → G ),((bijective f)∧ (bijective g)) → (bijective (g ∘ f)) := 
    assume (f:E → F ),
      assume (g:F → G ),
        assume (h1: (bijective f)∧ (bijective g)),
          have h2: bijective  f, from h1.left,
          have h3: bijective  g, from h1.right,
          have h4: injective  f, from h2.left,
          have h5: surjective f, from h2.right,
          have h6: injective  g, from h3.left,
          have h7: surjective g, from h3.right,
          have h8: injective  (g ∘ f), from composee_injections  f g (and.intro h4 h6),
          have h9: surjective (g ∘ f), from composee_surjections f g (and.intro h5 h7),
          show bijective  (g ∘ f), from and.intro h8 h9


  --§6.2 Image directe, image réciproque

  -- exercice 6.2.15
  -- Donnez une definition de Imf. 
  definition ensemble_image  (f: E → F)  := {y:F | ∃ x:E, y = f x }

  -- exercice 6.2.16
  -- Si α est un type, le type (set α) est le type des ensembles d'éléments de type α 
  -- On peut utiliser le symbole ∈ dans  x ∈ A  lorsque x est de type α  et que A est de type (set α)
  -- Donnez la définition d'image directe, image réciproque

  definition image_directe    (f: E → F) (A: set E) := {y:F | ∃ x:E, (x ∈ A) ∧ (y = f x) }
  definition image_reciproque (f: E → F) (B: set F) := {x:E | (f x)∈ B }

  -- exercice 6.2.17
  -- Montrez que f est surjective ssi Im f = (@set.univ F)  (l'ensemble de tous les elements de type F)
  #check set.ext
  #check @set.univ

  theorem reformulation_surjectivite : ∀  (f: E → F), (surjective f) ↔ (ensemble_image f = @set.univ F) :=
    assume f: E → F,
      iff.intro
        (assume h_f_surjective : surjective f, 
          set.ext  (
            assume y:F, 
              iff.intro  
                (assume h_y_in_im: y ∈ ensemble_image f,  
                  (trivial: y ∈ (@set.univ F))
                )  
                (assume h_y_in_set_univ: y ∈ (@set.univ F),  
                  show ∃ x:E, y = f x , from h_f_surjective y
                )
          ) 
        )
        (assume h_im_eq_F: ensemble_image f = @set.univ F,  assume y:F,  
          (
            have h_y_in_F : y ∈ @set.univ F, from trivial,
            show y ∈ (ensemble_image f) , from h_im_eq_F.symm ▸ h_y_in_F
          )
          
        )

  -- exercice 6.2.18

  theorem ex_6_2_18_1 : ∀ (f: E→ F) (g:F→ G) (A: set E), image_directe g (image_directe f A) = image_directe (g ∘ f) A := 
    assume (f: E→ F) (g:F→ G) (A: set E),
      set.ext (assume (z:G), iff.intro
        (
          assume (h_z_in_im_im : z ∈ image_directe g (image_directe f A) ), 
            exists.elim h_z_in_im_im (
              assume (y:F) (h_y_and : (y ∈ image_directe f A)∧ (z = g y) ),
                exists.elim h_y_and.left (
                  assume (x:E) (h_x_and : (x∈ A)∧ (y = f x)),
                  (
                    exists.intro (x:E) (
                      and.intro 
                        (h_x_and.left : x∈ A)
                        (show z = (g∘ f) x, from (h_x_and.right ▸ h_y_and.right : z = g (f x) ))
                    )
                  )
                )
            )
        )
        (
          assume (h_z_in_im_o  : z ∈ image_directe (g ∘ f) A ), 
            exists.elim h_z_in_im_o (
              assume (x:E) (h_x_and: (x∈ A) ∧ (z = g (f x))),
               exists.intro (f x : F) (
                 and.intro 
                   (show f x ∈ image_directe f A, from exists.intro (x:E) (and.intro (h_x_and.left:x∈ A) (eq.refl (f x)) ) )
                   (show z = g (f x),             from h_x_and.right                                                       )
               )
            )
        ) 
      )
  
  theorem ex_6_2_18_2 : ∀ (f: E→ F) (g:F→ G) (C: set G), image_reciproque f (image_reciproque g C) = image_reciproque (g ∘ f) C := 
    assume (f: E→ F) (g:F→ G) (C: set G),
      set.ext (assume (x:E), iff.intro
        (
          assume (h_x_in_imr_imr : x ∈ image_reciproque f (image_reciproque g C)), 
            have h_fx : f x ∈ (image_reciproque g C), from  h_x_in_imr_imr,
            have h_gfx: g (f x) ∈ C, from  h_fx,
            show (g ∘ f) x ∈ C, from h_gfx
        )
        (
          assume h_z_in_imr_o  : x ∈ image_reciproque (g ∘ f) C , 
            have h_gfx : g (f x) ∈ C, from h_z_in_imr_o,
            have h_fx  : f x ∈ (image_reciproque g C), from h_gfx,
            show x ∈ image_reciproque f (image_reciproque g C), from h_fx
        ) 
      )

  theorem ex_6_2_18_3 : ∀ (f: E→ F) (A: set E) (B: set E), image_directe f (A ∩ B) ⊆ (image_directe f A) ∩ (image_directe f B) := 
     assume  (f: E→ F) (A: set E) (B: set E), 
       assume (y:F) (h_yfAB : y ∈ image_directe f (A ∩ B)) ,
         exists.elim h_yfAB (
           assume (x:E) (h_x_and : x ∈ A ∩ B ∧ y = f x ),
            and.intro 
              (exists.intro (x:E) ( and.intro (h_x_and.left.left :x∈ A) (h_x_and.right : y = f x)))
              (exists.intro (x:E) ( and.intro (h_x_and.left.right:x∈ B) (h_x_and.right : y = f x)))
          )
         
  theorem ex_6_2_18_4 :  ∀ (f: E→ F) (A: set E) (B: set E), image_directe f (A ∪ B) = (image_directe f A) ∪ (image_directe f B) := 
     assume  (f: E→ F) (A: set E) (B: set E), 
      set.ext (assume (y:F), iff.intro 
        (assume (h_yfAB : y ∈ image_directe f (A ∪ B)) ,
          exists.elim h_yfAB (
            assume (x:E) (h_x_and : x ∈ A ∪ B ∧ y = f x ),
              or.elim h_x_and.left
                (assume (h_xA:x∈ A), or.inl  (exists.intro (x:E) (and.intro (h_xA:x∈ A) (h_x_and.right:y =f x))) )
                (assume (h_xB:x∈ B), or.inr  (exists.intro (x:E) (and.intro (h_xB:x∈ B) (h_x_and.right:y =f x))) )
            )
        )
        (
           assume h_yfAfB : y ∈ (image_directe f A) ∪ (image_directe f B),
            or.elim h_yfAfB
              (assume h_yfA: y ∈ (image_directe f A), 
                exists.elim h_yfA (
                  assume (x:E) (h_x_and: x∈ A ∧ y = f x), 
                    exists.intro (x:E) (and.intro ((or.inl h_x_and.left):x ∈ A ∪ B ) (h_x_and.right:y=f x))
                )
              )
              (assume h_yfB: y ∈ (image_directe f B), 
                exists.elim h_yfB (
                  assume (x:E) (h_x_and: x∈ B ∧ y = f x), 
                    exists.intro (x:E) (and.intro ((or.inr h_x_and.left):x ∈ A ∪ B ) (h_x_and.right:y=f x))
                )
              )
        )
      )

  theorem ex_6_2_18_5 : ∀ (f: E→ F) (H: set F) (K: set F), image_reciproque f (H ∩ K) = (image_reciproque f H) ∩ (image_reciproque f K) := 
     assume  (f: E→ F) (H: set F) (K: set F), 
      set.ext (assume (x:E), iff.intro 
        (
          assume h_xfm1HK : x ∈ image_reciproque f (H ∩ K) ,
            have h_fx : f x ∈ H ∩ K, from h_xfm1HK,
            show  x ∈ (image_reciproque f H) ∩ (image_reciproque f K) ,             
              from and.intro (h_fx.left : f x ∈ H) (h_fx.right : f x ∈ K)
        )
        (
          assume h_xfm1Hfm1K : x ∈ (image_reciproque f H) ∩ (image_reciproque f K) ,
            have h_fxH : f x ∈ H, from h_xfm1Hfm1K.left,
            have h_fxK : f x ∈ K, from h_xfm1Hfm1K.right,
            show x ∈ (image_reciproque f (H ∩ K) ) , from and.intro h_fxH h_fxK
        )
      )

  theorem ex_6_2_18_6 : ∀ (f: E→ F) (H: set F) (K: set F), image_reciproque f (H ∪ K) = (image_reciproque f H) ∪ (image_reciproque f K) := 
     assume  (f: E→ F) (H: set F) (K: set F), 
      set.ext (assume (x:E), iff.intro 
        (
          assume (h_xfm1HK : x ∈ image_reciproque f (H ∪ K)) ,
            have h_fx : f x ∈ H ∪ K, from h_xfm1HK,
            or.elim h_fx
              (assume h_fxH : f x ∈ H, or.inl h_fxH)
              (assume h_fxK : f x ∈ K, or.inr h_fxK)
        )
        (
          assume h_xfm1Hfm1K : x ∈ (image_reciproque f H) ∪ (image_reciproque f K) ,
            or.elim h_xfm1Hfm1K
              (assume h_fxH: f x ∈ H, or.inl h_fxH)
              (assume h_fxK: f x ∈ K, or.inr h_fxK)
        )
      )

  -- Construction let_in

  theorem exemple_let_in :  ∀ u:E → F,  ∀ v:F → G, surjective (v ∘  u) → (surjective v) := 
  assume (u:E → F) (v:F → G),
    assume h_v_o_u_surjective : surjective (v ∘  u)  , 
      assume (z:G),
        exists.elim (h_v_o_u_surjective z) (
          assume (x:E) (h_z_eq_v_o_u_x : z = (v ∘  u) x),
            let y: F := u x in exists.intro y (
              show z = v y, from h_z_eq_v_o_u_x
            )
        )

  -- Construction eq.subst
  theorem exemple_eq_subst : ∀ A:set E, ∀ B:set E, ∀ x:E, x ∈ A ∧ A=B → x ∈ B :=
    assume (A:set E) (B:set E), assume (x:E),
      assume (h: x ∈ A ∧ A=B),
        show x∈ B, from (h.right: A=B) ▸ (h.left: x∈ A )

  -- §6.3 : Caractérisations de l’injectivité et de la surjectivité

  -- exercice 6.3.19
  -- Image directe de l'image reciproque

  theorem ex_6_3_19_1 :  ∀  (f: E → F), ∀ (B:set F), ( (image_directe f (image_reciproque f B)) ⊆ B) :=
    assume (f: E → F),
      assume (B:set F),
        assume (y:F), assume (h_yB: y ∈ (image_directe f (image_reciproque f B))),
            exists.elim h_yB (
              assume (x:E), 
                assume (h_and : (x ∈ (image_reciproque f B)) ∧ (y = f x)),
                  (eq.symm h_and.right) ▸ (h_and.left: f x ∈ B)
            )



--  theorem ex_6_3_19_2 : ∀ (f: E → F), ∀ (B:set F),  (image_directe f (image_reciproque f B)) = B ∩ (image_directe f set.univ) :=
  theorem ex_6_3_19_2 : ∀ (f: E → F), ∀ (B:set F),  (image_directe f (image_reciproque f B)) = B ∩ (ensemble_image f) :=
    assume (f: E → F),
      assume (B:set F),
        set.ext (
          assume (y:F),        
            iff.intro
              ( 
                assume (h_yffm1B: y ∈ (image_directe f (image_reciproque f B))), 
                  exists.elim h_yffm1B (
                    assume (x:E) (h_x_and : x∈ image_reciproque f B ∧ y = f x),
                      and.intro
                        (show y ∈ B,                from h_x_and.right.symm ▸ (h_x_and.left: f x ∈ B) )
                        (show y ∈ ensemble_image f, from exists.intro x h_x_and.right)
                  )
              )
              (
                assume h_yBimF: y ∈ B ∩ (ensemble_image f) ,
                  exists.elim h_yBimF.right 
                  (
                    assume (x:E) (h_yfx : y= f x),
                      exists.intro x (
                        and.intro 
                          (
                            have h_fxB :  f x ∈ B,         from h_yfx ▸ h_yBimF.left,
                            show x ∈ image_reciproque f B, from h_fxB
                          )
                          (show y = f x, from h_yfx)
                      )
                  )
              )
        )


  -- Image réciproque de l'image directe
  theorem ex_6_3_19_3 : ∀ (f: E → F),  ∀ (A:set E), (A ⊆  (image_reciproque f (image_directe f A))) :=
    assume (f: E → F),
        assume (A:set E),
          assume (x:E), assume (h_xA: x ∈ A),
          show f x ∈ (image_directe f A), from exists.intro x ⟨ h_xA,  (eq.refl (f x)) ⟩


  -- exercice 6.3.20
-- Caracterisations de la surjectivité, de l'injectivité

  lemma ex_6_3_20_1_1 : ∀  (f: E → F),  (surjective f) → ∀ (H:set F), (H ⊆  (image_directe f (image_reciproque f H))) :=
    assume (f: E → F),
      assume (h: surjective f),
        assume (H:set F),
          assume (y:F), assume (h_yH: y ∈ H),
            exists.elim (h y)  (
              assume(x:E), assume (h_yfx:y= f x),
              have h_fxH: f x ∈ H, from h_yfx ▸ h_yH,
              have h_xiH: x ∈ (image_reciproque f H), from h_fxH,
              exists.intro x  ( and.intro  h_xiH h_yfx)  
            )

  lemma ex_6_3_20_1_2 :  ∀  f: E → F, ∀ A: set E, set.nonempty A → set.nonempty (image_directe f A) := 
    assume  (f: E → F) (A: set E),
      assume (hnA : set.nonempty A),
       exists.elim hnA (
         assume (v:E) (p:v ∈ A),
           exists.intro  (f v) (exists.intro v (and.intro p (eq.refl (f v))))
       )

  lemma ex_6_3_20_1_2a :  ∀  f: E → F, ∀ A: set E, nonempty A → nonempty (image_directe f A) := 
    assume  (f: E → F) (A: set E),
      assume (hnA : nonempty A),
       nonempty.elim hnA (
         assume (u: (subtype A)),
           nonempty.intro (subtype.mk (f u.val) (exists.intro u.val (and.intro u.property (eq.refl (f u.val)))))
       )

  lemma ex_6_3_20_1_3 :  ∀  f: E → F, ∀ A: set E,  set.nonempty (image_directe f A) → set.nonempty A := 
    assume  (f: E → F) (A: set E),
      assume (hnfA : set.nonempty (image_directe f A)),
       exists.elim hnfA (
         assume (y:F) (h_y_in_fA: y ∈  (image_directe f A) ),
           exists.elim h_y_in_fA (
             assume (x:E) (h_x_and : x∈ A ∧ y = f x),
               exists.intro  x h_x_and.left
           )
       )

#check ex_6_3_20_1_2
#check @set.not_nonempty_iff_eq_empty 
--#check @set.nonempty_iff_ne_empty 
#check @set.eq_empty_of_subset_empty
#check @set.singleton_nonempty
#check @set.subset_eq_empty
#check set.not_nonempty_iff_eq_empty.not_right.mpr
#check @set.eq_of_mem_singleton

  lemma ex_6_3_20_1_4 : ∀  (f: E → F), (∀ (H:set F), H ⊆  (image_directe f (image_reciproque f H)) ) →  (surjective f)   :=
    assume (f: E → F),
      assume (h_forall: ∀ (H:set F), H ⊆  (image_directe f (image_reciproque f H))),
        assume (y:F),
          let H:=({y}: set F) in
          have h_im_nonempty: set.nonempty (image_directe f (image_reciproque f H) ), from
            set.not_nonempty_iff_eq_empty.not_right.mpr (assume h_im_empty:image_directe f (image_reciproque f H) = ∅ , 
              absurd 
                   (set.singleton_nonempty y)
                   (set.not_nonempty_iff_eq_empty.mpr (set.subset_eq_empty (h_forall H) h_im_empty))),
          have h_imrec_nonempty : set.nonempty (image_reciproque f H), from ex_6_3_20_1_3 f  (image_reciproque f H) h_im_nonempty,
          exists.elim h_imrec_nonempty (
            assume (x:E) (h_x: x ∈ (image_reciproque f H)),
              exists.intro x (show y=f x, from (set.eq_of_mem_singleton h_x).symm)
          )

--  lemma L {α:Type} (A:set α) (B: set α) : A = B ↔ (A ⊆ B ∧ B ⊆ A) := by library_search
  #check subset_antisymm
  #check subset_antisymm_iff

  --lemma L  {α:Type} (A:set α) (B: set α) : A=B → A ⊆ B := λ h, h ▸ (subset_refl A)
--lemma L  {α:Type} (A:set α) (B: set α) : A=B → A ⊆ B := by library_search

  #check eq.subset 

  theorem ex_6_3_20_1 :  ∀  (f: E → F), (surjective f) ↔  (∀ (H:set F), H =  (image_directe f (image_reciproque f H)) )  := 
    assume (f: E → F),
      iff.intro
      (assume h_fsurj: surjective f, 
        assume H:set F,
          subset_antisymm 
            (ex_6_3_20_1_1 f h_fsurj H)
            (ex_6_3_19_1   f H )
      )
      (
        assume (h_forall :   ∀ (H:set F), H =  (image_directe f (image_reciproque f H)) ),
         ex_6_3_20_1_4 f (
           assume (H:set F), 
             eq.subset (h_forall H)
         )
      )



  lemma ex_6_3_20_2_1 : ∀  (f: E → F), (injective f) → (∀ (A:set E), ((image_reciproque f (image_directe f A)) ⊆ A)) :=
    assume (f: E → F),
      assume (h_inj: injective f),
        assume (A:set E),
          assume (x:E), assume (h_xfm1fA: x ∈ (image_reciproque f (image_directe f A))),
          have h_fxfA:f x ∈ (image_directe f A), from h_xfm1fA,
          exists.elim h_fxfA (
            assume(x':E), 
              assume ( h_x'A_and_fxfx' : (x'∈ A) ∧( f x = f x')),
                have h_xx': x=x', from h_inj x x' h_x'A_and_fxfx'.right,
                (eq.symm h_xx') ▸ h_x'A_and_fxfx'.left
          )
  --           assume ( ⟨ x':E, h_xA: x' ∈ A ⟩ :A) , assume (h_fxfx': f x = f x'),
  --           have h_xx': x=x', from h_inj x x' h_fxfx',
  --           (eq.symm h_xx') ▸ h_xA
  --         )

--instance : has_singleton α (set α) := ⟨λ a, {b | b = a}⟩
  #check @set.eq_of_mem_singleton
  #check @set.mem_singleton
  #check @rfl

  lemma ex_6_3_20_2_2 : ∀  (f: E → F), ∀ (x:E), (image_directe  f {x}) = {f x} := 
    assume (f: E → F),
      assume (x: E),
        set.ext (
          assume (y:F), 
            iff.intro 
--              (assume (h:y ∈ image_directe  f {x}), exists.elim h (assume (t:E), assume (h_t:t∈ {x} ∧ y= f t), (set.eq_of_mem_singleton h_t.left) ▸ h_t.right)) 
              (assume (h:y ∈ image_directe  f {x}), exists.elim h (assume (t:E), assume (h_t:t∈ {x} ∧ y= f t),  h_t.left ▸ h_t.right)) 
--              (assume (h:y ∈ {f x}) ,exists.intro x (and.intro ((eq.refl x) : (x∈ ({x}:(set E)))) (h: y = f x)  ))
--              (assume (h:y ∈ {f x}) ,exists.intro x (and.intro ((set.mem_singleton x) : (x∈ {x})) (h: y = f x)  ))
--              (assume (h:y ∈ {f x}) ,exists.intro x (and.intro (set.mem_singleton x)  (h: y = f x)  ))
              (assume (h:y ∈ {f x}) ,exists.intro x (and.intro (eq.refl x)  (h: y = f x)  ))
        )

  lemma ex_6_3_20_2_2' : ∀  (f: E → F), ∀ (x:E), (image_directe  f {x}) = {f x} := by {intros,  ext1, fconstructor,  intro h, cases h, finish, intro h, fconstructor, tauto, finish}
  
  lemma ex_6_3_20_2_3 : ∀  (f: E → F), (∀ (A:set E), ((image_reciproque f (image_directe f A)) ⊆ A))   → (injective f) :=
    assume (f: E → F),
      assume (h_forallset: ∀ (A:set E), (image_reciproque f (image_directe f A)) ⊆ A) ,
        assume (x:E) (x':E) (h_fx1x' : f x = f x'),
          let A := ({x}:set E) in
          have h_fm1fA : image_reciproque f {f x} ⊆ {x}, from  (ex_6_3_20_2_2 f x) ▸  (h_forallset A) , 
          have h_x'_in  : x' ∈ image_reciproque f {f x} , from h_fx1x'.symm,
          show x=x', from (h_fm1fA h_x'_in).symm

-- #check @eq.rec
--          have h_fm1fA : image_reciproque f {f x} ⊆ {x}, from  (@ex_6_3_20_2_2' _ _ f x)   ▸  (h_forallset {x}) , 
--          have h_fm1fA' : image_reciproque f {f x} ⊆ {x}, from  
--             @eq.rec (set F) (image_directe  f {x}) (λ B:set F, (image_reciproque f B) ⊆ ({x}:set E) ) (h_forallset {x})  { f x} 
--                     (@ex_6_3_20_2_2' _ _ f x)    , 
--          have h_x'_in  : x' ∈ image_reciproque f {f x} , from h.symm,


  #check subset_antisymm
  #check subset_antisymm_iff
  #check subset_refl
  #check @set.mem_singleton

  theorem ex_6_3_20_2 :  ∀  (f: E → F), (injective f) ↔  (∀ (A:set E), ((image_reciproque f (image_directe f A)) = A)) := 
     assume (f: E → F),
       iff.intro 
       (assume (h_inj: injective f), assume (A:set E), subset_antisymm (ex_6_3_20_2_1 f h_inj A) (ex_6_3_19_3 f A))
       (assume (h_forallset: ∀ (A:set E), (image_reciproque f (image_directe f A)) = A) ,ex_6_3_20_2_3 f (
           assume (A:set E), (h_forallset A).symm ▸ (subset_refl A)
         )
       )


  theorem ex_6_3_20_3 : ∀ (f: E → F),
       (surjective f) ↔ 
            (∀ B₁:set F, ∀ B₂:set F,
               ( ( (image_reciproque f B₁) ⊆  (image_reciproque f B₂)) → ( B₁ ⊆ B₂) )
            )
        :=
        assume (f: E → F) ,        
         iff.intro 
           (
              assume(h_surjective_f: surjective f),
                assume (B₁:set F), assume( B₂:set F ),
                  assume(h_imrec_subset: (image_reciproque f B₁) ⊆  (image_reciproque f B₂)),
                    assume (y), assume (h_yB1: y ∈ B₁),
                      show (y ∈ B₂), from 
                        exists.elim (h_surjective_f y) (
                           assume (x:E), assume (h_yfx: y = f x),
                             have h_fxB1 : (f x)∈ B₁, from (h_yfx ▸  h_yB1),
                             have h_xirB1: x ∈ (image_reciproque f B₁), from h_fxB1,
                             have h_xirB2: x ∈ (image_reciproque f B₂), from (set.mem_of_mem_of_subset h_xirB1 h_imrec_subset),
                             have h_fxB2 : (f x)∈ B₂, from h_xirB2,
                             have h_yB2  : y∈ B₂, from (( eq.symm h_yfx) ▸ h_fxB2),
                             h_yB2
                        )
                        
           )
           (
             assume(h_forall: ∀ B₁:set F, ∀ B₂:set F, ( ( (image_reciproque f B₁) ⊆  (image_reciproque f B₂)) → ( B₁ ⊆ B₂) )),
               assume(y:F), 
                  have h_syne: (set.nonempty {y}) , from  set.singleton_nonempty _,
                  have h_incl: _, from (mt (h_forall {y} ∅ ) ) (set.nonempty.not_subset_empty h_syne),
                  exists.elim ((set.not_subset ).mp h_incl) (
                     assume (x:E), assume(h_existsH:_),
                     exists.elim (h_existsH) (
                        assume (H:x ∈ (image_reciproque f {y} )),
                        assume (h_inutile: x ∉ (image_reciproque f ∅ )),
                        exists.intro x (
                            have h_fxy: (f x)∈ {y}, from H,
                            have h_iff:_, from @set.mem_singleton_iff F (f x) y,
                            show y=f x, from eq.symm (( h_iff.mp ) h_fxy)
                        )
                     )
                     
                  )
           )


  theorem ex_6_3_20_4 : 
    ∀ (f:E → F), (injective f)  ↔ (∀ A: set E, ∀ B: set E, image_directe f (A∩B) = (image_directe f A)∩ (image_directe f B)) 
    := 
    assume (f:E → F),
      iff.intro 
      (assume (h_f_injective : injective f), 
        assume (A:set E),
          assume (B:set E),
            subset_antisymm
              (ex_6_2_18_3 f A B)
              (
                assume (y:F) (h_y_in_inter : y ∈ (image_directe f A)∩ (image_directe f B) ),
                  exists.elim h_y_in_inter.left  (assume (xA:E) (h_xA_and: xA ∈ A ∧ y = f xA ) , 
                  exists.elim h_y_in_inter.right (assume (xB:E) (h_xB_and: xB ∈ B ∧ y = f xB ) , 
                  have h_fxA_eq_fxB  : f xA = f xB, from h_xA_and.right ▸ h_xB_and.right,
                  have h_xA_eq_xB    :   xA = xB,   from h_f_injective xA xB h_fxA_eq_fxB,
                  exists.intro xA (
                    and.intro 
                      (and.intro (h_xA_and.left: xA ∈ A) (  ( h_xA_eq_xB.symm ▸  h_xB_and.left): xA ∈ B) ) 
                      (h_xA_and.right : y = f xA)
                  )))
              )
      )
      (assume (h_forallsets : ∀ A: set E, ∀ B: set E, image_directe f (A∩B) = (image_directe f A)∩ (image_directe f B)), 
        assume (x x':E) (h_fx_eq_fx' : f x = f x'),
         let A:set E := {x} in let B:set E:={x'} in 
         have h_fx_in_inter : f x ∈ (image_directe f A)∩ (image_directe f B) ,from 
             and.intro 
               (exists.intro x (and.intro ((set.mem_singleton x) :x∈ A) (eq.refl (f x)) )) 
               (h_fx_eq_fx'.symm ▸  (exists.intro x' (and.intro ((set.mem_singleton x') :x'∈ B) (eq.refl (f x')))) ),
         have h_fAB_nonempty: set.nonempty (image_directe f (A∩B)), from 
           exists.intro (f x) (
              (h_forallsets A B).symm ▸ h_fx_in_inter
           ),
         have h_A_inter_B_nonempty : set.nonempty (A∩B), from ex_6_3_20_1_3 f (A∩B) h_fAB_nonempty,
         exists.elim h_A_inter_B_nonempty (
           assume (t:E) (h_tAB : t∈ A ∧ t∈ B),
            show x=x', from (h_tAB.left : t=x) ▸ (h_tAB.right: t=x')
         )
      )
        
#check @mt
lemma mt2 {a b : Prop} (h₁ : ¬b → ¬a) (h₂ : a) : b := by library_search
#check @not_imp_not
#print axioms not_imp_not
#print axioms decidable.not_imp_not

#check set.subset_empty_iff 
#check set.compl_empty

lemma ex_6_3_20_5_1 : ∀ f:E→ F, image_directe f ∅ = ∅ := assume (f:E→ F), (set.subset_empty_iff).mp ( -- (@set.subset_empty_iff F (image_directe f ∅)).mp (
    assume  (y:F) (h_y: y∈  image_directe f ∅), 
     exists.elim h_y (
       assume (x:E) (h_x: x∈ ∅ ∧ y = f x),
         show y∈ ∅ , from false.elim h_x.left
     )
  )
lemma ex_6_3_20_5_2 :  ∀ f:E→ F, ensemble_image f = image_directe f (@set.univ E) := 
  assume (f: E→ F), set.ext (assume (y:F), iff.intro
     (assume (h:y ∈ ensemble_image f ), exists.elim h (assume (x:E) (h_yfx:y=f x), exists.intro x (and.intro trivial h_yfx) ) ) 
     (assume (h:y ∈ image_directe f (@set.univ E) ), exists.elim h (assume (x:E) (h_y_and: x ∈ set.univ ∧ y = f x), exists.intro x h_y_and.right ) ))
   

  theorem ex_6_3_20_5 : ∀ f:E→ F, (bijective f) ↔ (∀ A:set E, image_directe f Aᶜ = (image_directe f A)ᶜ  ) := 
    assume f: E→ F,
      iff.intro
        (assume h_f_bijective:bijective f,
          assume A:set E,
            set.ext ( assume (y:F),
              iff.intro
                (assume h_y_in_f_Ac : y ∈ image_directe f Aᶜ,
                  assume h_y_in_fA:y ∈ (image_directe f A),
                    exists.elim h_y_in_f_Ac (
                      assume (x:E) (h_x_and : x∈Aᶜ ∧ y = f x ),
                        exists.elim h_y_in_fA (
                          assume (x':E) (h_x'_and : x'∈A ∧ y = f x' ),
                            have h_x_eq_x' : x=x', from (h_f_bijective.left : injective f) x x' (h_x_and.right ▸ h_x'_and.right) ,
                            absurd ((h_x_eq_x'.symm ▸ h_x'_and.left): x∈ A) (h_x_and.left : ¬ x∈ A)
                        )
                    )
                )
                (assume h_y_in_fA_c : y ∈ (image_directe f A)ᶜ,
                  exists.elim ((h_f_bijective.right : surjective f) y) (
                    assume (x:E) (h_yfx: y = f x),
                      have h_x_notin_A : x ∉ A, from (
                         assume (h_x_in_A: x∈ A),
                           absurd (exists.intro x (and.intro h_x_in_A h_yfx)) h_y_in_fA_c
                        ),
                      exists.intro x (and.intro h_x_notin_A h_yfx)
                  )
                )
            )
        )
        (assume h_forallset: (∀ A:set E, image_directe f Aᶜ = (image_directe f A)ᶜ  ),
          and.intro
            (assume (x x':E), 
              not_imp_not.mp
                 (assume  (h_x_ne_x' : x ≠  x'),
                   let A:set E:={x} in
                   have h_x'_notin_A: x' ∉ A, from (mt (@set.eq_of_mem_singleton _ x' x)) h_x_ne_x'.symm,
                   have h_fx'_in_fA_c: f x' ∈  (image_directe f A)ᶜ  , from 
                      (h_forallset A) ▸ (exists.intro x' (and.intro h_x'_notin_A (eq.refl (f x')) )),
                   show f x ≠ f x', from (
                     assume (h_fx_eq_fx': f x = f x'),
                      absurd (exists.intro x (and.intro (set.mem_singleton x) h_fx_eq_fx'.symm ) : ( f x' ∈  (image_directe f A))) h_fx'_in_fA_c
                   )
                 )
          )
            (
               (reformulation_surjectivite f).mpr (
                  calc
                    ensemble_image f = image_directe f ∅ᶜ    : (@set.compl_empty E).symm ▸ (ex_6_3_20_5_2 f)
                       ...           = (image_directe f ∅)ᶜ  : h_forallset ∅
                       ...           = (∅: set F)ᶜ           : congr_arg has_compl.compl (ex_6_3_20_5_1 f)
                       ...           = @set.univ F           : @set.compl_empty F

               )
            )
        )

  

  theorem ex_6_4_21_1 : ∀  (u: E → F) (v: F → G), (injective (v ∘  u) )→ (injective u) := 
  assume  (u: E → F) (v: F → G),
    assume (h_v_o_u_injective: injective (v ∘  u)),
      assume (x x':E), 
        assume  (h_ux_eq_ux':u x = u  x'),
          have h_vux_eq_vux' : v ( u x) = v (u x'), from congr_arg v h_ux_eq_ux',
          h_v_o_u_injective x x' h_vux_eq_vux'
          
  theorem ex_6_4_21_2 : ∀  (u: E → F) (v: F → G), (injective (v ∘  u) )→ (surjective u)→ (injective v)  := 
  assume  (u: E → F) (v: F → G),
    assume (h_v_o_u_injective: injective (v ∘  u) ),
      assume (h_u_surjective : surjective u),
        assume (y y':F),
          assume  (h_vy_eq_vy':v y = v y'),
            exists.elim (h_u_surjective y) ( 
              assume (x:E) (h_y_eq_ux : y = u x),
                exists.elim (h_u_surjective y') ( 
                  assume (x':E) (h_y'_eq_ux' : y' = u x'),
                    have h_vux_eq_vux' : v (u x)  = v (u x'), from  h_y'_eq_ux' ▸ h_y_eq_ux ▸ h_vy_eq_vy',
                    have h_x_eq_x'     : x=x',                from h_v_o_u_injective x x' h_vux_eq_vux',
                    show y =y',                               from  h_y_eq_ux.symm ▸ h_y'_eq_ux'.symm ▸ (congr_arg u h_x_eq_x')
                )
            )

  theorem ex_6_4_21_3 : ∀  (u: E → F) (v: F → G), surjective (v ∘  u) → (surjective v) := 
  assume  (u: E → F) (v: F → G),
    assume h_v_o_u_surjective : surjective (v ∘  u)  , 
      assume (z:G),
        exists.elim (h_v_o_u_surjective z) (
          assume (x:E) (h_z_eq_v_o_u_x : z = (v ∘  u) x),
            exists.intro (u x) (
              show z = v (u x), from h_z_eq_v_o_u_x
            )
        )

  theorem ex_6_4_21_4 : ∀  (u: E → F) (v: F → G), surjective (v ∘  u) → (injective v) → (surjective u) := 
  assume  (u: E → F) (v: F → G),
    assume h_v_o_u_surjective : surjective (v ∘  u),
      assume h_v_injective: injective v,
        assume (y:F),
          let z:= v y in
           exists.elim (h_v_o_u_surjective z)
           (
             assume (x:E) (h_z_eq_v_u_x: z = v (u x)) ,
             exists.intro x (
               show y = u x, from h_v_injective y (u x) h_z_eq_v_u_x
             )
           )

end sec6 




namespace sec6_court
  variables {E F G : Type}

  -- exercice 6.1.12 
  def injective  (f: E → F) := ∀ u v, ( f u = f v → u = v )
  def surjective (f: E → F) := ∀ y, ∃ x, y= f x
  def bijective  (f: E → F) := (injective f) ∧ (surjective f)

  -- exercice 6.1.13
  def identite : E → E := λ x, x 
  theorem identite_injective  : @injective  E E identite  := λ u v h , h
  theorem identite_surjective : @surjective E E identite  := λ y, ⟨y , rfl ⟩ 
  theorem identite_bijective  : @bijective E E identite := ⟨ identite_injective, identite_surjective ⟩ 

-- exercice 6.1.14
-- Montrez que la composée de deux applications injectives est injective
-- Idem pour surjectives, bijectives
  theorem composee_injections {f: E → F} {g : F → G} : (injective   f) →  (injective  g) → injective (g ∘ f) := 
    λ h1l h1r u v h2,  h1l u v (h1r (f u) (f v) h2)

  theorem composee_surjections  {f: E → F} {g : F → G} : (surjective f) →  (surjective g) → surjective (g ∘ f) := 
    λ h1l h1r z, let ⟨y,h3⟩ := h1r z in let ⟨x,h5⟩ := h1l y in ⟨ x, (h5 ▸ h3 : z = g (f x))⟩  --  ⟨ x, eq.trans h3 (congr_arg g h5)⟩ 

  theorem composee_bijections_court   {f: E → F} {g : F → G} : (bijective f) →  (bijective g) → bijective (g ∘ f) := 
    λ h1l h1r, ⟨ composee_injections h1l.left h1r.left,  composee_surjections h1l.right h1r.right ⟩ 

  --§6.2 Image directe, image réciproque

  -- exercice 6.2.15
  definition ensemble_image  (f: E → F)  := {y | ∃ x, y = f x }

  -- exercice 6.2.16
  definition image_directe    (f: E → F) (A: set E) := {y | ∃ x, (x ∈ A) ∧ (y = f x) }
  definition image_reciproque (f: E → F) (B: set F) := {x | (f x)∈ B }

  -- exercice 6.2.17


  -- Montrez que f est surjective ssi Im f = (@set.univ F)  (l'ensemble de tous les elements de type F)
  theorem reformulation_surjectivite'' {f: E → F} : (surjective f) ↔ (∀ y, y ∈ ensemble_image f) :=
    iff.rfl
  
  theorem reformulation_surjectivite' {f: E → F} : (surjective f) ↔ (ensemble_image f = set.univ) :=
    ⟨ λ h_f_surjective,  set.ext (λ y, ⟨ λ _, trivial, λ _, h_f_surjective y ⟩ ) ,(λ h_im_eq_F y, ( (h_im_eq_F.symm ▸ trivial):y ∈ (ensemble_image f) ) )⟩ 

  -- exercice 6.2.18

  theorem ex_6_2_18_1' {f: E→ F} {g:F→ G} {A: set E} : image_directe g (image_directe f A) = image_directe (g ∘ f) A := 
    set.ext (λ z, 
        ⟨  λ ⟨y, ⟨ ⟨x, ⟨ h_xA, h_yfx ⟩ ⟩, h_zgy ⟩ ⟩, ⟨x, ⟨h_xA, (h_yfx ▸ h_zgy : z = g (f x) ) ⟩ ⟩,
           λ ⟨x, ⟨h_xA, h_zgfx⟩ ⟩, ⟨ f x, ⟨ ⟨ x, ⟨h_xA, (eq.refl _) ⟩ ⟩, h_zgfx ⟩ ⟩ ⟩ 
      )

  theorem ex_6_2_18_2' {f: E→ F} {g:F→ G} {C: set G} : image_reciproque f (image_reciproque g C) = image_reciproque (g ∘ f) C := 
    set.ext (λ _, iff.rfl )

  theorem ex_6_2_18_2'' {f: E→ F} {g:F→ G} {C: set G} : image_reciproque f (image_reciproque g C) = image_reciproque (g ∘ f) C := 
    eq.refl _

  theorem ex_6_2_18_2''' {f: E→ F} {g:F→ G} {C: set G} :  image_reciproque f (image_reciproque g C) = image_reciproque (g ∘ f) C := 
    by tauto

  theorem ex_6_2_18_3' {f: E→ F} {A: set E} {B: set E} : image_directe f (A ∩ B) ⊆ (image_directe f A) ∩ (image_directe f B) := 
     λ _ ⟨x, h⟩, ⟨⟨x, ⟨h.1.1, h.2⟩⟩, ⟨x, ⟨h.1.2, h.2⟩ ⟩ ⟩ 

  theorem ex_6_2_18_4' {f: E→ F} {A: set E} {B: set E} : image_directe f (A ∪ B) = (image_directe f A) ∪ (image_directe f B) := 
     set.ext (λ y, ⟨ 
        ( λ ⟨x, h⟩ , or.elim h.1
              (λ h_xA, or.inl ⟨x, ⟨h_xA, h.2⟩ ⟩ )
              (λ h_xB, or.inr ⟨x, ⟨h_xB, h.2⟩ ⟩ ) ),
        ( λ h_yfAfB, or.elim h_yfAfB
              (λ ⟨x, h⟩, ⟨x, ⟨or.inl h.1, h.2⟩ ⟩ )
              (λ ⟨x, h⟩, ⟨x, ⟨or.inr h.1, h.2⟩ ⟩ ) )
        ⟩
      )

  theorem ex_6_2_18_5' {f: E→ F} {H: set F } {K: set F} : image_reciproque f (H ∩ K) = (image_reciproque f H) ∩ (image_reciproque f K) :=   
    set.ext (λ _, iff.rfl)

  theorem ex_6_2_18_5'' {f: E→ F} {H: set F } {K: set F} : image_reciproque f (H ∩ K) = (image_reciproque f H) ∩ (image_reciproque f K) := 
    eq.refl _

  theorem ex_6_2_18_6' {f: E→ F} {H: set F} {K: set F} : image_reciproque f (H ∪ K) = (image_reciproque f H) ∪ (image_reciproque f K) := 
    set.ext (λ _, iff.rfl)

  theorem ex_6_2_18_6'' {f: E→ F} {H: set F} {K: set F} : image_reciproque f (H ∪ K) = (image_reciproque f H) ∪ (image_reciproque f K) := 
    eq.refl _

-- exercice 6.3.19
  -- Image directe de l'image reciproque

  theorem ex_6_3_19_1'  {f: E → F} {B:set F} :  (image_directe f (image_reciproque f B)) ⊆ B :=
      λ _ ⟨x,h⟩, (eq.symm h.2) ▸ h.1

  theorem ex_6_3_19_2' {f: E → F} {B:set F} : (image_directe f (image_reciproque f B)) = B ∩ (ensemble_image f) :=
    set.ext (λ y, ⟨λ ⟨x, h⟩, ⟨h.2.symm ▸ h.1, ⟨x, h.2⟩ ⟩, λ ⟨h_yB,⟨x, h_yfx⟩ ⟩, ⟨x,⟨ (h_yfx ▸ h_yB : f x ∈ B), h_yfx⟩ ⟩ ⟩)

  theorem ex_6_3_19_3' {f: E → F}  {A:set E} : A ⊆  (image_reciproque f (image_directe f A)) :=
      λ x h, ⟨  x , ⟨ h,  eq.refl _ ⟩⟩ 

  lemma ex_6_3_20_1_1' {f: E → F}  :  (surjective f) → ∀ (H:set F), (H ⊆  (image_directe f (image_reciproque f H))) :=
      λ h H y h_yH, let ⟨ x, h_yfx⟩ :=h y in  ⟨  x  , ⟨ ( h_yfx ▸ h_yH : f x ∈ H ) ,h_yfx ⟩ ⟩ 

  lemma ex_6_3_20_1_2'  {f: E → F} {A: set E} : set.nonempty A → set.nonempty (image_directe f A) := 
      λ   ⟨ v,p⟩ ,  ⟨ f v, ⟨v, ⟨p, eq.refl _ ⟩ ⟩ ⟩  

  lemma ex_6_3_20_1_2a'  {f: E → F} {A: set E} : nonempty A → nonempty (image_directe f A) := 
      λ  ⟨ ⟨ v,p⟩ ⟩, ⟨ ⟨ f v, ⟨v, ⟨p, eq.refl _ ⟩ ⟩ ⟩ ⟩ 

  lemma ex_6_3_20_1_3'  {f: E → F} {A: set E} : set.nonempty (image_directe f A) → set.nonempty A := 
      λ  ⟨ _,⟨x,h⟩ ⟩, ⟨x, h.1⟩ 
           
  lemma ex_6_3_20_1_4' {f: E → F} : (∀ (H:set F), H ⊆  (image_directe f (image_reciproque f H)) ) →  (surjective f)   :=
      λ  h_forall y, let  ⟨ x,h_x⟩ :=
            ex_6_3_20_1_3' (set.not_nonempty_iff_eq_empty.not_right.mpr (assume h_im_empty , 
                absurd (set.singleton_nonempty y) (set.not_nonempty_iff_eq_empty.mpr (set.subset_eq_empty (h_forall {y}) h_im_empty)))  )            
           in ⟨  x, (set.eq_of_mem_singleton h_x).symm ⟩ 

  theorem ex_6_3_20_1' {f: E → F} :  (surjective f) ↔  (∀ (H:set F), H =  (image_directe f (image_reciproque f H)) )  := 
      ⟨ 
        λ  h_fsurj H, subset_antisymm (ex_6_3_20_1_1'  h_fsurj H) ex_6_3_19_1'  ,
        λ  h_forall, ex_6_3_20_1_4'  (λ H, eq.subset (h_forall H))
      ⟩ 

  lemma ex_6_3_20_2_1' {f: E → F} :  (injective f) → (∀ (A:set E), ((image_reciproque f (image_directe f A)) ⊆ A)) :=
      λ  h_inj A x ⟨x',h ⟩, (h_inj x x' h.2).symm ▸ h.1

  lemma ex_6_3_20_2_2' {f: E → F}  {x:E} :  (image_directe  f {x}) = {f x} := 
        set.ext ( λ y,  ⟨  (λ ⟨ t, h_t⟩ , h_t.1 ▸ h_t.2) , (λ h ,⟨  x,  ⟨  rfl ,h  ⟩  ⟩ ) ⟩ )

  lemma ex_6_3_20_2_3' {f: E → F} :  (∀ (A:set E), ((image_reciproque f (image_directe f A)) ⊆ A))   → (injective f) :=
      λ  h_f x x' h_x,  ((((@ex_6_3_20_2_2' _ _ f x)   ▸  (h_f {x})): image_reciproque f {f x} ⊆  {x}) h_x.symm).symm

  theorem ex_6_3_20_2' {f: E → F} :  (injective f) ↔  (∀ (A:set E), ((image_reciproque f (image_directe f A)) = A)) := 
       ⟨  (λ  h_i A, subset_antisymm (ex_6_3_20_2_1'  h_i A) ex_6_3_19_3' ), (λ  h_f ,ex_6_3_20_2_3'  ( λ  A, (h_f A).symm ▸ (subset_refl A) ) )       ⟩ 


  theorem ex_6_3_20_3' {f: E → F} :
       (surjective f) ↔  (∀ B₁:set F, ∀ B₂:set F,  ( ( (image_reciproque f B₁) ⊆  (image_reciproque f B₂)) → ( B₁ ⊆ B₂) ) )
        := ⟨ λ h_surjective_f B₁ B₂ h_imrec_subset y h_yB1, let ⟨ x,h_yfx⟩ := (h_surjective_f y) in 
                (( eq.symm h_yfx) ▸ ((h_imrec_subset (((h_yfx ▸  h_yB1): (f x)∈ B₁):(x ∈ (image_reciproque f B₁))) ):(x ∈ (image_reciproque f B₂)))),           
             λ h_forall y,
                  let ⟨ x, ⟨ H, h_inutile⟩ ⟩ := (set.not_subset.mp ((mt (h_forall {y} ∅ ) ) (set.nonempty.not_subset_empty (set.singleton_nonempty y)))) 
                  in  ⟨  x, eq.symm (( (@set.mem_singleton_iff F (f x) y).mp ) H) ⟩ 
           ⟩ 



  theorem ex_6_3_20_4' {f:E → F} : (injective f)  ↔ (∀ A: set E, ∀ B: set E, image_directe f (A∩B) = (image_directe f A)∩ (image_directe f B))  := 
      ⟨ λ  h_f_injective A B, 
            subset_antisymm ex_6_2_18_3'  (
                λ  y ⟨ ⟨xA ,h_xA_and⟩, ⟨xB ,h_xB_and⟩⟩, ⟨ xA, ⟨ ⟨ h_xA_and.left, (h_f_injective xA xB (h_xA_and.right ▸ h_xB_and.right)).symm ▸ h_xB_and.left ⟩, h_xA_and.right ⟩ ⟩ 
              ),
      (λ h_forallsets x x' h_fx_eq_fx', 
         let A:set E := {x} in let B:set E:={x'} in 
         have h_fx_in_inter : f x ∈ (image_directe f A)∩ (image_directe f B) ,from 
             ⟨  
               ⟨  x, ⟨  ((set.mem_singleton x) :x∈ A) , eq.refl (f x) ⟩  ⟩  ,
               (h_fx_eq_fx'.symm ▸ ⟨x', ⟨ ((set.mem_singleton x') :x'∈ B), eq.refl (f x')⟩  ⟩  )
             ⟩ ,
         have h_fAB_nonempty: set.nonempty (image_directe f (A∩B)), from 
           ⟨  (f x) , (
              (h_forallsets A B).symm ▸ h_fx_in_inter
           )⟩ ,
         let ⟨t , h_tAB⟩ := ex_6_3_20_1_3' h_fAB_nonempty in  h_tAB.left ▸ h_tAB.right
      )⟩ 
        
lemma ex_6_3_20_5_1' {f:E→ F} : image_directe f ∅ = ∅ := 
  set.subset_empty_iff.mp (λ y ⟨x ,h_x⟩, false.elim h_x.left)

lemma ex_6_3_20_5_2' {f:E→ F} : ensemble_image f = image_directe f set.univ := 
  set.ext (λ y, ⟨ (λ ⟨x, h_yfx⟩, ⟨x, ⟨trivial,h_yfx⟩  ⟩ ),  (λ ⟨x, ⟨_,h_yfx ⟩ ⟩, ⟨ x, h_yfx ⟩ ) ⟩ )
   
theorem ex_6_3_20_5' {f:E→ F} : (bijective f) ↔ (∀ A:set E, image_directe f Aᶜ = (image_directe f A)ᶜ ) := 
      ⟨ λ  h_f_bijective A, set.ext ( λ y,
              ⟨ λ ⟨x ,h_x_and⟩ ⟨x' ,h_x'_and⟩, absurd (((h_f_bijective.1  x x' (h_x_and.2 ▸ h_x'_and.2) ).symm ▸ h_x'_and.1): x∈ A) h_x_and.1,
                λ  h_y_in_fA_c, let ⟨x, h_yfx⟩:=h_f_bijective.right y in
                      ⟨x, ⟨ (λ  h_x_in_A, absurd (exists.intro x (and.intro h_x_in_A h_yfx)) h_y_in_fA_c), h_yfx ⟩  ⟩ 
--                      ⟨x, ⟨ (λ h_x_in_A, absurd (⟨x, ⟨ h_x_in_A, h_yfx ⟩ ⟩: y∈ image_directe f A)  h_y_in_fA_c), h_yfx ⟩  ⟩ 
              ⟩ ),
        (λ  h_forallset, ⟨ λ x x', not_imp_not.mp (λ (h_x_ne_x' : x ≠  x'), λ  h_fx_eq_fx', absurd 
                        (⟨ x, ⟨ set.mem_singleton x, h_fx_eq_fx'.symm ⟩ ⟩                                                       : (f x' ∈  (image_directe f {x})) )   
                        (((h_forallset {x}) ▸ ⟨x', ⟨ (mt (@set.eq_of_mem_singleton _ x' x)) h_x_ne_x'.symm, eq.refl (f x') ⟩ ⟩ ): (f x' ∈  (image_directe f {x})ᶜ))
                 ),
               reformulation_surjectivite'.mpr ( calc
                    ensemble_image f = image_directe f ∅ᶜ    : (@set.compl_empty E).symm ▸ ex_6_3_20_5_2'
                       ...           = (image_directe f ∅)ᶜ  : h_forallset ∅
                       ...           = (∅: set F)ᶜ           : congr_arg has_compl.compl ex_6_3_20_5_1'
                       ...           = @set.univ F           : set.compl_empty
               )
            ⟩ 
        ) ⟩ 

  section sec_6_4_21_1_court

  variables {u: E → F} {v: F → G}

  theorem ex_6_4_21_1' : (injective (v ∘  u) )→ (injective u) := 
    λ h_inj x x' h_eq, h_inj x x' (congr_arg _ h_eq : (v (u x) = v (u x')) )
          
  theorem ex_6_4_21_2' : (injective (v ∘  u) )→ (surjective u)→ (injective v)  := 
    λ h_vuinj h_usurj y y' h_eq, let ⟨x, h_yux⟩ := h_usurj y in let ⟨x', h_y'ux' ⟩ := h_usurj y' in 
      h_yux.symm ▸ h_y'ux'.symm ▸ (congr_arg _ (h_vuinj x x' (h_y'ux' ▸ h_yux ▸ h_eq : v (u x) = v (u x'))))

  theorem ex_6_4_21_3' :  surjective (v ∘  u) → (surjective v) := 
    λ h_vu_surj z,  let ⟨ x, h_zvux⟩ := h_vu_surj z in ⟨ u x , h_zvux ⟩ 

  theorem ex_6_4_21_4' :  surjective (v ∘  u) → (injective v) → (surjective u) := 
    λ h_vusurj h_vinj y, let ⟨x,h_vyvux⟩ := h_vusurj (v y) in  ⟨ x, h_vinj y (u x) h_vyvux ⟩ 

  end sec_6_4_21_1_court

end sec6_court


namespace sec7


  definition suite := ℕ → ℝ 
  
  definition suite_add (u:suite) (v:suite) : suite := λ n:ℕ , ((u n) + (v n) )
  instance suite_has_add : has_add suite :=⟨suite_add⟩

  definition suite_mul (u:suite) (v:suite) : suite := λ n:ℕ , ((u n) * (v n) )
  instance suite_has_mul : has_mul suite :=⟨suite_mul⟩


  definition converge_vers (u:suite) (ℓ : ℝ) : Prop := ∀ ε:ℝ, ε >0 →  ∃ n₀ : ℕ , ∀ n:ℕ, n ≥ n₀ → |u n - ℓ| ≤ ε
  definition converge (u:suite) : Prop := ∃  ℓ : ℝ, converge_vers u ℓ 


  #check (abs_add : ∀ a b : ℝ, abs (a + b) ≤ abs a + abs b)

--#check @div_le_div
--#check @div_le_div''
--#check @div_le_div_left
--#check @div_le_div_left'
#check @div_le_div_right
--#check @div_le_div_right'
--#check @div_le_div_iff
--#check @div_le_div_iff'
#check @abs_nonneg
#check @zero_lt_three
#check @lt_or_eq_of_le
#check @div_eq_iff
#check @abs_eq_zero
#check @eq_of_sub_eq_zero
#check @div_mul_cancel

--lemma L {a:ℝ} {b:ℝ }  : |a-b| = |b-a| := by library_search
#check @abs_sub_comm
--lemma L {a:ℝ} {b:ℝ }  : max a b ≥ b := by library_search
#check @le_max_right
--#check add_self_div_two
--lemma L {a:ℝ}  : a+a = a*2 := by library_search
#check @mul_two

#check @mul_le_mul
#check @mul_le_mul_iff_right
#check @mul_le_mul_left
#check @mul_le_mul_right
--#check @nat.not_succ_le_self
--lemma L   : ¬ (3:ℝ )≤ 2 := by norm_num
--#print L
#check @zero_div

  lemma not_three_le_two  : ¬ (3:ℝ )≤ 2 := not_le_of_gt (norm_num.lt_bit0_bit1 _ _ (le_refl 1))

  theorem unicite_limite : ∀ (u:suite), ∀ ℓ ℓ': ℝ, (converge_vers u ℓ)∧(converge_vers u ℓ') → ℓ = ℓ' :=
   assume (u:suite), 
    assume ℓ ℓ': ℝ, 
      assume h_cv: (converge_vers u ℓ)∧(converge_vers u ℓ'),
        let ε := | ℓ' - ℓ | /3 in
          have h_ε_ge_0: 0 ≤ ε , from  trans_rel_right (≤) (zero_div 3).symm ((div_le_div_right zero_lt_three).mpr (abs_nonneg (ℓ' - ℓ ))),
          or.elim (lt_or_eq_of_le h_ε_ge_0)
          (assume h_ε_gt_0: ε >0, 
            exists.elim (h_cv.left ε h_ε_gt_0) (
              assume (n0:ℕ ) (h_n0: ∀ n:ℕ, n ≥ n0 → |u n - ℓ| ≤ ε),
              exists.elim (h_cv.right ε h_ε_gt_0) (
                assume (n1:ℕ ) (h_n1: ∀ n:ℕ, n ≥ n1 → |u n - ℓ'| ≤ ε),
                let n2:=max n0 n1 in
                have h_3ε_eq_2ε: ε*3 ≤ ε*2, from
                  calc
                    ε*3   = | ℓ' - ℓ |                          : div_mul_cancel (| ℓ' - ℓ |) (three_ne_zero: (3:ℝ ) ≠ 0) 
                      ... = | (ℓ' - (u n2))  +  ((u n2) - ℓ) |  : by abel
                      ... ≤ | (ℓ' - (u n2))| +| ((u n2) - ℓ) |  : abs_add _ _ 
                      ... = | ((u n2) - ℓ')| +| ((u n2) - ℓ) |  : (abs_sub_comm ℓ' (u n2)) ▸ (eq.refl _)
                      ... ≤  ε + ε                              : add_le_add (h_n1 n2 (le_max_right n0 n1)) (h_n0 n2 (le_max_left n0 n1))
                      ... = ε * 2                               : (mul_two ε ).symm ,
                  --by linarith
                  absurd  ((mul_le_mul_left h_ε_gt_0 ).mp h_3ε_eq_2ε)  not_three_le_two
              )
            )
          )
          (assume h_ε_eq_0: 0 =ε, 
            have h_dℓℓ' : | ℓ' - ℓ |=0, from 
              calc 
                | ℓ' - ℓ |=0*3 : (div_eq_iff (three_ne_zero: (3:ℝ )≠ 0)).mp h_ε_eq_0.symm
                ...      =0    : zero_mul 3 ,
            have h_ℓℓ': ℓ' - ℓ = 0, from abs_eq_zero.mp h_dℓℓ',
            (eq_of_sub_eq_zero h_ℓℓ').symm
          )


  theorem unicite_limite' {u:suite} {ℓ ℓ': ℝ} :  (converge_vers u ℓ)∧(converge_vers u ℓ') → ℓ = ℓ' :=
      assume h_cv: (converge_vers u ℓ)∧(converge_vers u ℓ'),
        let ε := | ℓ' - ℓ | /3 in
          have h_ε_ge_0: 0 ≤ ε , from trans_rel_right (≤) (zero_div 3).symm ((div_le_div_right zero_lt_three).mpr (abs_nonneg (ℓ' - ℓ ))),
          or.elim (lt_or_eq_of_le h_ε_ge_0)
          (assume h_ε_gt_0: ε >0, 
            exists.elim (h_cv.left ε h_ε_gt_0) (
              assume (n0:ℕ ) (h_n0: ∀ n:ℕ, n ≥ n0 → |u n - ℓ| ≤ ε),
              exists.elim (h_cv.right ε h_ε_gt_0) (
                assume (n1:ℕ ) (h_n1: ∀ n:ℕ, n ≥ n1 → |u n - ℓ'| ≤ ε),
                let n2:=max n0 n1 in
                have h_3ε_eq_2ε: ε*3 ≤ ε*2, from
                  calc
                    ε*3   = | ℓ' - ℓ |                          : div_mul_cancel (| ℓ' - ℓ |) (three_ne_zero: (3:ℝ ) ≠ 0) 
                      ... = | (ℓ' - (u n2))  +  ((u n2) - ℓ) |  : by abel
                      ... ≤ | (ℓ' - (u n2))| +| ((u n2) - ℓ) |  : abs_add _ _ 
                      ... = | ((u n2) - ℓ')| +| ((u n2) - ℓ) |  : by simp [abs_sub_comm]
                      ... ≤  ε + ε                              : add_le_add (h_n1 n2 (le_max_right n0 n1)) (h_n0 n2 (le_max_left n0 n1))
                      ... = ε * 2                               : by linarith,
                  by linarith
              )
            )
          )
          (assume h_ε_eq_0: 0 =ε, 
            have h_dℓℓ' : | ℓ' - ℓ |=0, from 
              calc 
                | ℓ' - ℓ |=0*3 : (div_eq_iff (three_ne_zero: (3:ℝ )≠ 0)).mp h_ε_eq_0.symm
                ...      =0    : zero_mul 3 ,

            have h_ℓℓ': ℓ' - ℓ = 0, from abs_eq_zero.mp h_dℓℓ',
            (eq_of_sub_eq_zero h_ℓℓ').symm -- by linarith
          )




   theorem lt_div2 (x:ℝ ) (y:ℝ ) (h: x<y) : (x/2) < (y/2) := (div_lt_div_right zero_lt_two).mpr h

   theorem deux_moities (u:ℝ ) : (u/2)+(u/2) = u := 
      calc
        (u/2) + (u/2) = (u/2)*1+ (u/2)*1 : (eq.symm (mul_one (u/2))) ▸ (eq.refl ((u/2) + (u/2)))
        ...           = (u/2)*(1+1)      : eq.symm (mul_add _ _ _)
        ...           = (u/2)*2          : congr_arg (λ (z:ℝ ), (u/2)*z) (eq.refl _)
        ...           = u                : div_mul_cancel u two_ne_zero

  theorem sumlim (u:suite) (v:suite)  (ℓ : ℝ ) (ℓ' : ℝ ) : ((converge_vers u ℓ) ∧   (converge_vers v ℓ')) → (converge_vers (u+v) (ℓ+ℓ')):= 
  (λ (h1: (converge_vers u ℓ) ∧   (converge_vers v ℓ') ),
      assume (ε:ℝ)   (hε : ε >0) , 
        have hε2: (0 < (ε /2)),  from   (zero_div 2 : (0/2 = (0:ℝ) )) ▸  (lt_div2 0 ε hε ),  --from trans_rel_right  (<)   (zero_div 2).symm   (lt_div2 0 ε hε ),

        exists.elim (h1.left  (ε/2)  hε2  )
          (assume (n0:ℕ) ,  assume (h2 : ∀ (n:ℕ ), n ≥ n0 → |u n - ℓ| ≤ ε/2 ),  
            exists.elim (h1.right  (ε/2)  hε2 )
            (assume (n1:ℕ), assume (h3 :  ∀ (n:ℕ ), n ≥ n1 → |v n - ℓ'| ≤ ε/2 )  ,
              let n2:=(max n0 n1) in exists.intro n2 (
                assume (n:ℕ ),
                assume (h4: n ≥ n2),          
                calc
                    |(u+v) n - (ℓ + ℓ')| = |(u n + v n ) - (ℓ + ℓ')     |   : eq.refl _ 
                    ...                 = |(u n + v n ) - ℓ - ℓ'       |   : congr_arg abs (sub_add_eq_sub_sub (u n + v n ) ℓ ℓ' )
                    ...                 = | (u n + v n ) + -ℓ - ℓ'     |   : (sub_eq_add_neg (u n + v n ) ℓ )        ▸ (eq.refl _)
                    ...                 = | u n + v n  + -ℓ + -ℓ'      |   : (sub_eq_add_neg (u n + v n  + -ℓ) ℓ' )  ▸ (eq.refl _)
                    ...                 = | u n + ( v n + -ℓ) + -ℓ'    |   : (add_assoc (u n) (v n)  (-ℓ))           ▸ (eq.refl _)
                    ...                 = | u n + ( -ℓ + v n) + -ℓ'    |   : (add_comm (-ℓ ) (v n))                  ▸ (eq.refl _)
                    ...                 = | (u n +  -ℓ) + v n + -ℓ'    |   : (add_assoc (u n) (-ℓ ) (v n))           ▸ (eq.refl _)
                    ...                 = | (u n +  -ℓ) + (v n + -ℓ')  |   : (add_assoc (u n +  -ℓ) (v n) (-ℓ' ) )   ▸ (eq.refl _)
                    ...                 = |(u n - ℓ ) + (v n - ℓ' )    |   : (sub_eq_add_neg (u n) ℓ ) ▸ (sub_eq_add_neg (v n) ℓ' )  ▸ (eq.refl _)
                    ...                 ≤ |(u n - ℓ )| + |(v n - ℓ' )| : abs_add _ _
                    ...                 ≤ ε/2 + ε/2 : add_le_add 
                                                    (h2 n ( ge_trans h4  (le_max_left  n0 n1) ))
                                                    (h3 n ( ge_trans h4  (le_max_right n0 n1) )) 
                    ...                 = ε : deux_moities ε 

              ) 
            )
          )
  )

  
  theorem sumlim' (u:suite) (v:suite)  (ℓ : ℝ ) (ℓ' : ℝ ) : ((converge_vers u ℓ) ∧   (converge_vers v ℓ')) → (converge_vers (u+v) (ℓ+ℓ')):= 
  (assume (h1: (converge_vers u ℓ) ∧   (converge_vers v ℓ') ),
      assume (ε:ℝ)   (hε : ε >0) , 
        have hε2: (0 < (ε /2)) , from  (by simp : (0/2) = (0:ℝ )) ▸  (lt_div2 (0:ℝ) ε hε  ),

      exists.elim (h1.left  (ε/2)  hε2   )
      (assume (n0:ℕ) ,  assume (h2 : ∀ (n:ℕ ), n ≥ n0 → |u n - ℓ| ≤ ε/2 ),  
        exists.elim (h1.right  (ε/2)  hε2 )
        (
          assume (n1:ℕ), assume (h3 :  ∀ (n:ℕ ), n ≥ n1 → |v n - ℓ'| ≤ ε/2 )  ,
          let n2:=(max n0 n1) in exists.intro n2 (
            assume (n:ℕ ) (h4: n ≥ n2),          
            calc
                |(u+v) n - (ℓ + ℓ')| = |(u n - ℓ ) + (v n - ℓ' ) |   :  by abel
                ...                 ≤ |(u n - ℓ )| + |(v n - ℓ' )|   : abs_add _ _
                ...                 ≤ ε/2 + ε/2 : 
                                              add_le_add 
                                                (h2 n ( ge_trans h4 ( le_max_left  _ _) ))
                                                (h3 n ( ge_trans h4 ( le_max_right _ _) )) 

                ...                 = ε : by linarith
          ) 
        )

      )
  )

end sec7