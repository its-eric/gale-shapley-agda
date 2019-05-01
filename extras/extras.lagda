module extras where

{--
freeMen+nLemma : ∀ man prefs freeMen engagedMen → lengthPrefs freeMen + 0 ≤′ suc (lengthPrefs ((man , prefs) ∷ freeMen) + lengthPrefs engagedMen)
freeMen+nLemma man prefs [] [] = z≤′n
freeMen+nLemma man prefs [] (x ∷ engagedMen) = z≤′n
freeMen+nLemma man [] (x ∷ freeMen) [] = ≤⇒≤′ (n≤1+n _)
freeMen+nLemma man (x₁ ∷ prefs) (x ∷ freeMen) [] = n≤2+m+n (length prefs) (foldr (λ _ → suc) 0 (proj₂ x) + lengthPrefs freeMen)
freeMen+nLemma man [] (x ∷ freeMen) (x₁ ∷ engagedMen) = ≤⇒≤′ (n-plus-zero≤1+n+m (lengthPrefs (x₁ ∷ engagedMen)) (lengthPrefs (x ∷ freeMen)))
freeMen+nLemma man (x₂ ∷ prefs) ((fst , []) ∷ freeMen) ((fst₁ , []) ∷ engagedMen) = ≤′-step (freeMen+nLemma fst₁ prefs freeMen engagedMen)
freeMen+nLemma man (x₂ ∷ prefs) ((fst , []) ∷ freeMen) ((fst₁ , x ∷ snd₁) ∷ engagedMen) = {!!}
freeMen+nLemma man (x₂ ∷ prefs) ((fst , x ∷ snd) ∷ freeMen) ((fst₁ , []) ∷ engagedMen) = {!!}
freeMen+nLemma man (x₂ ∷ prefs) ((fst , x ∷ snd) ∷ freeMen) ((fst₁ , x₁ ∷ snd₁) ∷ engagedMen) = {!!}
-}

{-- this is for correctness:
-- stepInv : (m : MatchingState) → Inv m → Inv (step m)

Something like:

data GaleShapleyInv : (m : MatchingState) → Set where
  inv : m ∈ m.listMen → w ∈ m.listWomen → b ∉ l(a) → (∃ a′ ∈ m : a′ ≻_{b} a ∨ p(a) = b
-}
