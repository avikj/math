{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- DecTable — point-update algebra over an arbitrary discrete index.
-- decRec definition reduces under goal-level `with`; proofs use the
-- fixed-codomain dispatch idiom verified in Diamond.Tables.
------------------------------------------------------------------------

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary using (Dec ; yes ; no ; ¬_ ; Discrete ; decRec)
open import Cubical.Data.Empty as Empty using (⊥)

module DecTable (Ix : Type) (_≟_ : Discrete Ix) where

  private variable A : Type

  update : Ix → A → (Ix → A) → (Ix → A)
  update i v f k = decRec (λ _ → v) (λ _ → f k) (i ≟ k)

  update-hit : {A : Type} (i k : Ix) (v : A) (f : Ix → A) → i ≡ k → update i v f k ≡ v
  update-hit i k v f p with i ≟ k
  ... | yes _ = refl
  ... | no ¬p = Empty.rec (¬p p)

  update-miss : {A : Type} (i k : Ix) (v : A) (f : Ix → A) → ¬ i ≡ k → update i v f k ≡ f k
  update-miss i k v f ¬p with i ≟ k
  ... | yes p = Empty.rec (¬p p)
  ... | no  _ = refl

  update-at : {A : Type} (i : Ix) (v : A) (f : Ix → A) → update i v f i ≡ v
  update-at i v f = update-hit i i v f refl

  update-comm : {A : Type} (i j : Ix) (v w : A) (f : Ix → A) → ¬ i ≡ j
    → update i v (update j w f) ≡ update j w (update i v f)
  update-comm {A} i j v w f ¬p = funExt point
    where
    point : (k : Ix) → update i v (update j w f) k ≡ update j w (update i v f) k
    point k = lemma (i ≟ k) (j ≟ k)
      where
      lemma : Dec (i ≡ k) → Dec (j ≡ k)
            → update i v (update j w f) k ≡ update j w (update i v f) k
      lemma (yes ik) (yes jk) = Empty.rec (¬p (ik ∙ sym jk))
      lemma (yes ik) (no ¬jk) =
        update-hit i k v (update j w f) ik
        ∙ sym (update-miss j k w (update i v f) ¬jk ∙ update-hit i k v f ik)
      lemma (no ¬ik) (yes jk) =
        update-miss i k v (update j w f) ¬ik ∙ update-hit j k w f jk
        ∙ sym (update-hit j k w (update i v f) jk)
      lemma (no ¬ik) (no ¬jk) =
        update-miss i k v (update j w f) ¬ik ∙ update-miss j k w f ¬jk
        ∙ sym (update-miss j k w (update i v f) ¬jk ∙ update-miss i k v f ¬ik)

  ----------------------------------------------------------------------
  -- Batch layer (decRec-based find/writes), built from atomic hit/miss
  -- so everything reduces; writes-comm for disjoint-domain batches.
  ----------------------------------------------------------------------
  open import Cubical.Data.List using (List ; [] ; _∷_)
  open import Cubical.Data.Maybe using (Maybe ; nothing ; just ; ¬nothing≡just)
  open import Cubical.Data.Sigma
  open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)

  find : {A : Type} → List (Ix × A) → Ix → Maybe A
  find []             k = nothing
  find ((i , v) ∷ ws) k = decRec (λ _ → just v) (λ _ → find ws k) (i ≟ k)

  writes : {A : Type} → List (Ix × A) → (Ix → A) → (Ix → A)
  writes []             f = f
  writes ((i , v) ∷ ws) f = update i v (writes ws f)

  find-hit : {A : Type} (i k : Ix) (v : A) (ws : List (Ix × A))
    → i ≡ k → find ((i , v) ∷ ws) k ≡ just v
  find-hit i k v ws p with i ≟ k
  ... | yes _ = refl
  ... | no ¬p = Empty.rec (¬p p)

  find-miss : {A : Type} (i k : Ix) (v : A) (ws : List (Ix × A))
    → ¬ i ≡ k → find ((i , v) ∷ ws) k ≡ find ws k
  find-miss i k v ws ¬p with i ≟ k
  ... | yes p = Empty.rec (¬p p)
  ... | no  _ = refl

  -- writes agrees with the base off the batch domain, and equals the
  -- batch value on it.  Returned as a ⊎ of explicit equations (no goal
  -- reduction needed at the use site).
  writes-char : {A : Type} (ws : List (Ix × A)) (f : Ix → A) (k : Ix)
    → ((find ws k ≡ nothing) × (writes ws f k ≡ f k))
    ⊎ (Σ[ v ∈ A ] (find ws k ≡ just v) × (writes ws f k ≡ v))
  writes-char []             f k = inl (refl , refl)
  writes-char ((i , v) ∷ ws) f k = go (i ≟ k)
    where
    go : Dec (i ≡ k)
       → ((find ((i , v) ∷ ws) k ≡ nothing) × (writes ((i , v) ∷ ws) f k ≡ f k))
       ⊎ (Σ[ w ∈ _ ] (find ((i , v) ∷ ws) k ≡ just w) × (writes ((i , v) ∷ ws) f k ≡ w))
    go (yes p) = inr (v , find-hit i k v ws p
                        , update-hit i k v (writes ws f) p)
    go (no ¬p) with writes-char ws f k
    ... | inl (fn , we) =
      inl ( find-miss i k v ws ¬p ∙ fn
          , update-miss i k v (writes ws f) ¬p ∙ we )
    ... | inr (w , fj , we) =
      inr ( w , find-miss i k v ws ¬p ∙ fj
              , update-miss i k v (writes ws f) ¬p ∙ we )

  -- disjoint-domain batches commute.
  writes-comm : {A : Type} (ws vs : List (Ix × A)) (f : Ix → A)
    → ((k : Ix) → (find ws k ≡ nothing) ⊎ (find vs k ≡ nothing))
    → writes ws (writes vs f) ≡ writes vs (writes ws f)
  writes-comm ws vs f disj = funExt point
    where
    fromJust : {A : Type} → A → Maybe A → A
    fromJust d nothing  = d
    fromJust d (just x) = x
    ji : {A : Type} {x y : A} → just x ≡ just y → x ≡ y
    ji {x = x} p = cong (fromJust x) p
    point : (k : Ix) → writes ws (writes vs f) k ≡ writes vs (writes ws f) k
    point k with writes-char ws (writes vs f) k | writes-char vs (writes ws f) k
    ... | inl (wn , we) | inl (vn , ve) = we ∙ lem ∙ sym ve
      where
      lem : writes vs f k ≡ writes ws f k
      lem with writes-char vs f k | writes-char ws f k
      ... | inl (_ , e1) | inl (_ , e2) = e1 ∙ sym e2
      ... | inl (_ , e1) | inr (w , fw , e2) = Empty.rec (¬nothing≡just (sym wn ∙ fw))
      ... | inr (w , fw , e1) | _ = Empty.rec (¬nothing≡just (sym vn ∙ fw))
    ... | inl (wn , we) | inr (v , vj , ve) = we ∙ lem ∙ sym ve
      where
      lem : writes vs f k ≡ v
      lem with writes-char vs f k
      ... | inl (vn , _) = Empty.rec (¬nothing≡just (sym vn ∙ vj))
      ... | inr (w , fw , e) = e ∙ ji (sym fw ∙ vj)
    ... | inr (v , vj , ve) | inl (vn , e) = ve ∙ lem ∙ sym e
      where
      lem : v ≡ writes ws f k
      lem with writes-char ws f k
      ... | inl (wn , _) = Empty.rec (¬nothing≡just (sym wn ∙ vj))
      ... | inr (w , fw , e') = ji (sym vj ∙ fw) ∙ sym e'
    ... | inr (v , vj , _) | inr (w , wj , _) with disj k
    ... | inl n = Empty.rec (¬nothing≡just (sym n ∙ vj))
    ... | inr n = Empty.rec (¬nothing≡just (sym n ∙ wj))
