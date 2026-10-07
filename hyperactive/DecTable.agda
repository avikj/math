{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- DecTable — point-update algebra over an arbitrary discrete index.
-- decRec definition reduces under goal-level `with`; proofs use the
-- fixed-codomain dispatch idiom verified in Diamond.Tables.
------------------------------------------------------------------------

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary using (Dec ; yes ; no ; ¬_ ; Discrete ; decRec)
open import Cubical.Data.Empty as Empty using (⊥)

module DecTable (I : Type) (_≟_ : Discrete I) where

  private variable A : Type

  update : I → A → (I → A) → (I → A)
  update i v f k = decRec (λ _ → v) (λ _ → f k) (i ≟ k)

  update-hit : {A : Type} (i k : I) (v : A) (f : I → A) → i ≡ k → update i v f k ≡ v
  update-hit i k v f p with i ≟ k
  ... | yes _ = refl
  ... | no ¬p = Empty.rec (¬p p)

  update-miss : {A : Type} (i k : I) (v : A) (f : I → A) → ¬ i ≡ k → update i v f k ≡ f k
  update-miss i k v f ¬p with i ≟ k
  ... | yes p = Empty.rec (¬p p)
  ... | no  _ = refl

  update-at : {A : Type} (i : I) (v : A) (f : I → A) → update i v f i ≡ v
  update-at i v f = update-hit i i v f refl

  update-comm : {A : Type} (i j : I) (v w : A) (f : I → A) → ¬ i ≡ j
    → update i v (update j w f) ≡ update j w (update i v f)
  update-comm {A} i j v w f ¬p = funExt point
    where
    point : (k : I) → update i v (update j w f) k ≡ update j w (update i v f) k
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
