{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Vyavāya — three attested pratyāhāras force a twice-recited sound, in
-- every possible line; Pini's choice of that sound is ha.
--
-- SOURCE for the term.  Pini, *Adhyy* 8.4.2 (~500 BCE):
--
--     a-ku-pu--num-vyavye 'pi
--
-- *vyavāya* is intervention — the sūtra says ṇatva goes through EVEN WITH
-- certain sounds standing between.  Nothing of 8.4.2's content is claimed
-- here; the term is taken for the phenomenon this file is about, a sound
-- standing between two others and blocking what contiguity would give.
-- And the sūtra opens with aṬ — which is one of the three classes below.
-- The class that names the interveners is itself a party to the
-- obstruction this file checks.
--
-- WHAT IS ALREADY CHECKED.  `NaturalMachine/
-- PratyaharaBuysTotalityWithLocality` proved that repeating a letter
-- DESTROYS locality of naming — repetition as a cost.  `NaturalMachine/
-- TheSecondNaIsTheCollision` computed the doubled A-marker's ambiguity
-- at aṆ — repetition as a collision.  `Krama_NoRecitationOrderSeats-
-- TheCycle…` proved on three abstract sounds that the three pair-classes
-- are unnameable in any recited-once line, and its header notes that
-- the ATTESTED family contains that cycle on {h y }.  This file proves it.
--
-- WHAT IS PROVED, on the actual fourteen Mhevara-stras, all 57 tokens:
--
--   §5  the line is encoded whole (`रेखा`, length 57, checked), and the
--       three attested pratyhras compute by refl:
--         aṬ  (a…Mṭ)  = a i u ṛ ḷ e o ai au h y v r     (13 sounds)
--         śaL (ś…Ml)  = ś ṣ s h                          (4 sounds)
--         yaR (y…Mr)  = the 32 consonants without h
--       and their restrictions to {h y } are the three pairs
--       {h y}, {ś h}, {y ś} — the Krama cycle, attested.
--
--   §6  `एकश्रुतौ-त्रयम्-असाध्यम्` — for ANY line ℓ over this alphabet
--       whose {h y }-subsequence is one of the six permutations (i.e.
--       h, y,  each recited exactly once), NO choice of three
--       start/marker pairs names classes restricting to those three
--       pairs.  Not an enumeration of lines: the proof is
--         class ⟹ contiguous factor of ℓ        (§3, list induction)
--         factor restricts to factor              (keep-++, §2)
--         factor of a 3-permutation never has the outer pair as its
--         {h y }-content                          (§4, the ten splits of
--                                                  each permutation,
--                                                  enumerated with a
--                                                  completeness proof)
--       So the theorem quantifies over infinitely many lines and closes.
--
--   §7  `हयशाः-रेखायाम्` — the real line's {h y ś}-subsequence is
--       h y ś h: NOT one of the six.  `रेखा-न-एकश्रुतिः` checks it is
--       outside the theorem's hypothesis — as it must be, since (§5) it
--       names the trio.
--
-- READ TOGETHER: the attested trio cannot exist over any line reciting
-- h, y,  once each.  Some one of the three must be said twice.  Pini
-- said ha — sūtra 5, ha ya va ra Ṭ, and sūtra 14, ha L — one seat before
-- ya for aṬ, one seat after śa for śaL, and the stretch y…Mr between
-- them h-free for yaR.  Three constraints, one repetition.  So the
-- doubled ha, whose COST the modules above measured (locality lost,
-- naming collides), is not thrift and not accident: it is the price of
-- the trio, and the line pays it because nothing cheaper exists.
--
-- §§2ℓ4 are inductions; every concrete
-- claim is refl.
------------------------------------------------------------------------

module Vyavaya_TheAttestedTrioForcesATwiceRecitedSoundAndPaninisChoiceIsHa where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; _and_ ; _or_ ; if_then_else_ ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; map ; length)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing) renaming (rec to mbRec)
open import Cubical.Data.Sigma using (Σ ; _,_ ; fst ; snd ; _×_)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Nat using (ℕ ; suc ; zero ; injSuc ; snotz)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)

private
  variable
    A B : Type₀

------------------------------------------------------------------------
-- §1  Generic Bool, Maybe and membership machinery.  Defined before the
--     alphabet so no variable here can collide with a constructor.
------------------------------------------------------------------------

anyL : (A → Bool) → List A → Bool
anyL f₀ []        = false
anyL f₀ (x₀ ∷ xs) = f₀ x₀ or anyL f₀ xs

allL : (A → Bool) → List A → Bool
allL f₀ []        = true
allL f₀ (x₀ ∷ xs) = f₀ x₀ and allL f₀ xs

and-true₁ : (b₁ b₂ : Bool) → (b₁ and b₂) ≡ true → b₁ ≡ true
and-true₁ true  b₂ _  = refl
and-true₁ false b₂ pf = ⊥rec (true≢false (sym pf))

and-true₂ : (b₁ b₂ : Bool) → (b₁ and b₂) ≡ true → b₂ ≡ true
and-true₂ true  b₂ pf = pf
and-true₂ false b₂ pf = ⊥rec (true≢false (sym pf))

-- Maybe discrimination and injectivity, self-contained
caseM : Maybe A → Type₀
caseM nothing  = Unit
caseM (just _) = ⊥

nothing≢justL : {x₀ : A} → nothing ≡ just x₀ → ⊥
nothing≢justL pf = subst caseM pf tt

fromML : Maybe (List A) → List A
fromML nothing   = []
fromML (just xs) = xs

justInjL : {xs ys : List A} → just xs ≡ just ys → xs ≡ ys
justInjL = cong fromML

-- propositional membership: no decidable equality, hence no soundness debt
_∈ᴸ_ : A → List A → Type₀
x₀ ∈ᴸ []        = ⊥
x₀ ∈ᴸ (y₀ ∷ ys) = (x₀ ≡ y₀) ⊎ (x₀ ∈ᴸ ys)

∈ᴸ-++ˡ : {x₀ : A} (xs ys : List A) → x₀ ∈ᴸ xs → x₀ ∈ᴸ (xs ++ ys)
∈ᴸ-++ˡ (y₀ ∷ xs) ys (inl pth) = inl pth
∈ᴸ-++ˡ (y₀ ∷ xs) ys (inr mm) = inr (∈ᴸ-++ˡ xs ys mm)

∈ᴸ-++ʳ : {x₀ : A} (xs ys : List A) → x₀ ∈ᴸ ys → x₀ ∈ᴸ (xs ++ ys)
∈ᴸ-++ʳ []        ys mm = mm
∈ᴸ-++ʳ (y₀ ∷ xs) ys mm = inr (∈ᴸ-++ʳ xs ys mm)

∈ᴸ-map : {x₀ : A} (g₀ : A → B) (xs : List A) → x₀ ∈ᴸ xs → g₀ x₀ ∈ᴸ map g₀ xs
∈ᴸ-map g₀ (y₀ ∷ xs) (inl pth) = inl (cong g₀ pth)
∈ᴸ-map g₀ (y₀ ∷ xs) (inr mm) = inr (∈ᴸ-map g₀ xs mm)

cMap : (A → List B) → List A → List B
cMap f₀ []        = []
cMap f₀ (x₀ ∷ xs) = f₀ x₀ ++ cMap f₀ xs

∈ᴸ-cMap : {x₀ : A} {y₀ : B} (f₀ : A → List B) (xs : List A)
        → x₀ ∈ᴸ xs → y₀ ∈ᴸ f₀ x₀ → y₀ ∈ᴸ cMap f₀ xs
∈ᴸ-cMap {x₀ = x₀} {y₀ = y₀} f₀ (z₀ ∷ xs) (inl pth) mmY =
  ∈ᴸ-++ˡ (f₀ z₀) (cMap f₀ xs) (subst (λ w₀ → y₀ ∈ᴸ f₀ w₀) pth mmY)
∈ᴸ-cMap f₀ (z₀ ∷ xs) (inr mm) mmY =
  ∈ᴸ-++ʳ (f₀ z₀) (cMap f₀ xs) (∈ᴸ-cMap f₀ xs mm mmY)

∈ᴸ-lookup : {x₀ : A} (f₀ : A → Bool) (xs : List A)
          → x₀ ∈ᴸ xs → allL f₀ xs ≡ true → f₀ x₀ ≡ true
∈ᴸ-lookup f₀ (y₀ ∷ xs) (inl pth) alEq =
  cong f₀ pth ∙ and-true₁ (f₀ y₀) (allL f₀ xs) alEq
∈ᴸ-lookup f₀ (y₀ ∷ xs) (inr mm) alEq =
  ∈ᴸ-lookup f₀ xs mm (and-true₂ (f₀ y₀) (allL f₀ xs) alEq)

------------------------------------------------------------------------
-- §2  Filtering and splitting, with completeness.
------------------------------------------------------------------------

keep : (A → Bool) → List A → List A
keep t₀ []        = []
keep t₀ (x₀ ∷ xs) = if t₀ x₀ then x₀ ∷ keep t₀ xs else keep t₀ xs

assoc³ : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
assoc³ []        ys zs = refl
assoc³ (x₀ ∷ xs) ys zs = cong (x₀ ∷_) (assoc³ xs ys zs)

keep-++ : (t₀ : A → Bool) (xs ys : List A)
        → keep t₀ (xs ++ ys) ≡ keep t₀ xs ++ keep t₀ ys
keep-++ t₀ []        ys = refl
keep-++ t₀ (x₀ ∷ xs) ys = branch (t₀ x₀)
  where
  branch : (b₀ : Bool)
         → (if b₀ then x₀ ∷ keep t₀ (xs ++ ys) else keep t₀ (xs ++ ys))
         ≡ (if b₀ then x₀ ∷ keep t₀ xs else keep t₀ xs) ++ keep t₀ ys
  branch true  = cong (x₀ ∷_) (keep-++ t₀ xs ys)
  branch false = keep-++ t₀ xs ys

keep-++₃ : (t₀ : A → Bool) (us qs ws : List A)
         → keep t₀ (us ++ qs ++ ws) ≡ keep t₀ us ++ keep t₀ qs ++ keep t₀ ws
keep-++₃ t₀ us qs ws =
  keep-++ t₀ us (qs ++ ws) ∙ cong (keep t₀ us ++_) (keep-++ t₀ qs ws)

-- every two-way split, and every three-way split, with completeness
splits2 : List A → List (List A × List A)
splits2 []        = ([] , []) ∷ []
splits2 (x₀ ∷ xs) = ([] , x₀ ∷ xs) ∷ map (λ pr → (x₀ ∷ fst pr , snd pr)) (splits2 xs)

splits2-complete : (ps ss : List A) → (ps , ss) ∈ᴸ splits2 (ps ++ ss)
splits2-complete []        []        = inl refl
splits2-complete []        (x₀ ∷ ss) = inl refl
splits2-complete (x₀ ∷ ps) ss =
  inr (∈ᴸ-map (λ pr → (x₀ ∷ fst pr , snd pr)) (splits2 (ps ++ ss))
              (splits2-complete ps ss))

allSplits : List A → List (List A × (List A × List A))
allSplits ℓs = cMap (λ pr → map (λ pr₂ → (fst pr , pr₂)) (splits2 (snd pr))) (splits2 ℓs)

allSplits-complete : (us qs ws : List A)
                   → (us , (qs , ws)) ∈ᴸ allSplits (us ++ qs ++ ws)
allSplits-complete us qs ws =
  ∈ᴸ-cMap (λ pr → map (λ pr₂ → (fst pr , pr₂)) (splits2 (snd pr)))
          (splits2 (us ++ qs ++ ws))
          (splits2-complete us (qs ++ ws))
          (∈ᴸ-map (λ pr₂ → (us , pr₂)) (splits2 (qs ++ ws)) (splits2-complete qs ws))

------------------------------------------------------------------------
-- §3  The extractor over an abstract alphabet, and: whatever it returns
--     is a contiguous factor of the line.  No occurrence of the start or
--     marker is identified — only the SHAPE of the result is used, so no
--     soundness of the boolean equality is ever needed.
------------------------------------------------------------------------

module Kartana (Aₖ : Type₀) (eqₖ : Aₖ → Aₖ → Bool) where

  prefixBefore : Aₖ → List Aₖ → Maybe (List Aₖ)
  prefixBefore mk []        = nothing
  prefixBefore mk (x₀ ∷ xs) =
    if eqₖ x₀ mk
    then just []
    else mbRec nothing (λ rs → just (x₀ ∷ rs)) (prefixBefore mk xs)

  suffixFromLast : Aₖ → List Aₖ → Maybe (List Aₖ)
  suffixFromLast st []        = nothing
  suffixFromLast st (x₀ ∷ xs) =
    mbRec (if eqₖ x₀ st then just (x₀ ∷ xs) else nothing) just (suffixFromLast st xs)

  klassL : Aₖ → Aₖ → List Aₖ → Maybe (List Aₖ)
  klassL st mk ℓs = mbRec nothing (λ ps → suffixFromLast st ps) (prefixBefore mk ℓs)

  -- a successful prefix is a prefix
  prefix-factor : (mk : Aₖ) (ℓs ps : List Aₖ)
                → prefixBefore mk ℓs ≡ just ps
                → Σ (List Aₖ) (λ ws → ℓs ≡ ps ++ ws)
  prefix-factor mk []        ps ee = ⊥rec (nothing≢justL ee)
  prefix-factor mk (x₀ ∷ xs) ps ee = branch (eqₖ x₀ mk) ee
    where
    inner : (mv : Maybe (List Aₖ)) → prefixBefore mk xs ≡ mv
          → mbRec nothing (λ rs → just (x₀ ∷ rs)) mv ≡ just ps
          → Σ (List Aₖ) (λ ws → x₀ ∷ xs ≡ ps ++ ws)
    inner nothing   mveq ee′ = ⊥rec (nothing≢justL ee′)
    inner (just rs) mveq ee′ =
      let ih = prefix-factor mk xs rs mveq
      in fst ih
       , (cong (x₀ ∷_) (snd ih) ∙ cong (_++ fst ih) (justInjL ee′))
    branch : (b₀ : Bool)
           → (if b₀ then just [] else mbRec nothing (λ rs → just (x₀ ∷ rs)) (prefixBefore mk xs)) ≡ just ps
           → Σ (List Aₖ) (λ ws → x₀ ∷ xs ≡ ps ++ ws)
    branch true  ee′ = (x₀ ∷ xs) , cong (_++ (x₀ ∷ xs)) (justInjL ee′)
    branch false ee′ = inner (prefixBefore mk xs) refl ee′

  -- a successful suffix is a suffix
  suffix-factor : (st : Aₖ) (ps qs : List Aₖ)
                → suffixFromLast st ps ≡ just qs
                → Σ (List Aₖ) (λ us → ps ≡ us ++ qs)
  suffix-factor st []        qs ee = ⊥rec (nothing≢justL ee)
  suffix-factor st (x₀ ∷ xs) qs ee = inner (suffixFromLast st xs) refl ee
    where
    branch : (b₀ : Bool)
           → (if b₀ then just (x₀ ∷ xs) else nothing) ≡ just qs
           → Σ (List Aₖ) (λ us → x₀ ∷ xs ≡ us ++ qs)
    branch true  ee′ = [] , justInjL ee′
    branch false ee′ = ⊥rec (nothing≢justL ee′)
    inner : (mv : Maybe (List Aₖ)) → suffixFromLast st xs ≡ mv
          → mbRec (if eqₖ x₀ st then just (x₀ ∷ xs) else nothing) just mv ≡ just qs
          → Σ (List Aₖ) (λ us → x₀ ∷ xs ≡ us ++ qs)
    inner nothing   mveq ee′ = branch (eqₖ x₀ st) ee′
    inner (just rs) mveq ee′ =
      let ih = suffix-factor st xs rs mveq
      in (x₀ ∷ fst ih)
       , (cong (x₀ ∷_) (snd ih) ∙ cong ((x₀ ∷ fst ih) ++_) (justInjL ee′))

  -- THE SHAPE: a named class is a contiguous factor of the line.
  klassL-factor : (st mk : Aₖ) (ℓs qs : List Aₖ)
                → klassL st mk ℓs ≡ just qs
                → Σ (List Aₖ) (λ us → Σ (List Aₖ) (λ ws → ℓs ≡ us ++ qs ++ ws))
  klassL-factor st mk ℓs qs ee = inner (prefixBefore mk ℓs) refl ee
    where
    inner : (mv : Maybe (List Aₖ)) → prefixBefore mk ℓs ≡ mv
          → mbRec nothing (λ ps → suffixFromLast st ps) mv ≡ just qs
          → Σ (List Aₖ) (λ us → Σ (List Aₖ) (λ ws → ℓs ≡ us ++ qs ++ ws))
    inner nothing   mveq ee′ = ⊥rec (nothing≢justL ee′)
    inner (just ps) mveq ee′ =
      let pf = prefix-factor mk ℓs ps mveq
          sf = suffix-factor st ps qs ee′
      in fst sf , fst pf
       , (snd pf ∙ cong (_++ fst pf) (snd sf) ∙ assoc³ (fst sf) qs (fst pf))

------------------------------------------------------------------------
-- §4  The alphabet: all forty-two sounds and all fourteen it-occurrences
--     of the Mhevara-stras.  ha is ONE constructor; its two seats are
--     two positions in the line.  The two A-markers are two occurrences
--     (Mṇ₁, Mṇ₂) — the granularity `TheSecondNaIsTheCollision` computed.
------------------------------------------------------------------------

data Varṇa : Type where
  a i u ṛ ḷ e o ai au                             : Varṇa   -- sūtras 1–4
  h y v r l ñ m ṅ ṇ n                             : Varṇa   -- sūtras 5–7
  jh bh gh ḍh dh j b g ḍ d                        : Varṇa   -- sūtras 8–10
  kh ph ch ṭh th c ṭ t k p ś ṣ s                  : Varṇa   -- sūtras 11–13
  Mṇ₁ Mk Mṅ Mc Mṭ Mṇ₂ Mm Mñ Mṣ Mś Mv My Mr Ml    : Varṇa   -- the fourteen its

eqV : Varṇa → Varṇa → Bool
eqV a a = true ; eqV i i = true ; eqV u u = true ; eqV ṛ ṛ = true
eqV ḷ ḷ = true ; eqV e e = true ; eqV o o = true ; eqV ai ai = true
eqV au au = true ; eqV h h = true ; eqV y y = true ; eqV v v = true
eqV r r = true ; eqV l l = true ; eqV ñ ñ = true ; eqV m m = true
eqV ṅ ṅ = true ; eqV ṇ ṇ = true ; eqV n n = true ; eqV jh jh = true
eqV bh bh = true ; eqV gh gh = true ; eqV ḍh ḍh = true ; eqV dh dh = true
eqV j j = true ; eqV b b = true ; eqV g g = true ; eqV ḍ ḍ = true
eqV d d = true ; eqV kh kh = true ; eqV ph ph = true ; eqV ch ch = true
eqV ṭh ṭh = true ; eqV th th = true ; eqV c c = true ; eqV ṭ ṭ = true
eqV t t = true ; eqV k k = true ; eqV p p = true ; eqV ś ś = true
eqV ṣ ṣ = true ; eqV s s = true
eqV Mṇ₁ Mṇ₁ = true ; eqV Mk Mk = true ; eqV Mṅ Mṅ = true ; eqV Mc Mc = true
eqV Mṭ Mṭ = true ; eqV Mṇ₂ Mṇ₂ = true ; eqV Mm Mm = true ; eqV Mñ Mñ = true
eqV Mṣ Mṣ = true ; eqV Mś Mś = true ; eqV Mv Mv = true ; eqV My My = true
eqV Mr Mr = true ; eqV Ml Ml = true
eqV _ _ = false

open Kartana Varṇa eqV

isMarker : Varṇa → Bool
isMarker Mṇ₁ = true ; isMarker Mk = true ; isMarker Mṅ = true
isMarker Mc = true ; isMarker Mṭ = true ; isMarker Mṇ₂ = true
isMarker Mm = true ; isMarker Mñ = true ; isMarker Mṣ = true
isMarker Mś = true ; isMarker Mv = true ; isMarker My = true
isMarker Mr = true ; isMarker Ml = true
isMarker _ = false

isSound : Varṇa → Bool
isSound x₀ = not (isMarker x₀)

-- the three witnesses of the obstruction
tHYŚ : Varṇa → Bool
tHYŚ h = true
tHYŚ y = true
tHYŚ ś = true
tHYŚ _ = false

-- {h y }-content of a stretch, as three bits (h? , y? , ?)
data Sig₃ : Type where
  sg₃ : Bool → Bool → Bool → Sig₃

occV : Varṇa → List Varṇa → Bool
occV tg xs = anyL (λ x₀ → eqV x₀ tg) xs

sig₃ : List Varṇa → Sig₃
sig₃ xs = sg₃ (occV h xs) (occV y xs) (occV ś xs)

eqB : Bool → Bool → Bool
eqB true  b₀ = b₀
eqB false b₀ = not b₀

eqSig₃ : Sig₃ → Sig₃ → Bool
eqSig₃ (sg₃ p₁ p₂ p₃) (sg₃ r₁ r₂ r₃) = eqB p₁ r₁ and (eqB p₂ r₂ and eqB p₃ r₃)

हय-युगम् शह-युगम् यश-युगम् : Sig₃
हय-युगम् = sg₃ true  true  false
शह-युगम् = sg₃ true  false true
यश-युगम् = sg₃ false true  true

------------------------------------------------------------------------
-- §5  The whole line, and the attested trio computed from it.
------------------------------------------------------------------------

रेखा : List Varṇa
रेखा = a ∷ i ∷ u ∷ Mṇ₁                                    -- 1  a i u Ṇ
     ∷ ṛ ∷ ḷ ∷ Mk                                         -- 2  ṛ ḷ K
     ∷ e ∷ o ∷ Mṅ                                         -- 3  e o Ṅ
     ∷ ai ∷ au ∷ Mc                                       -- 4  ai au C
     ∷ h ∷ y ∷ v ∷ r ∷ Mṭ                                 -- 5  ha ya va ra Ṭ
     ∷ l ∷ Mṇ₂                                            -- 6  la Ṇ
     ∷ ñ ∷ m ∷ ṅ ∷ ṇ ∷ n ∷ Mm                             -- 7  ña ma ṅa ṇa na M
     ∷ jh ∷ bh ∷ Mñ                                       -- 8  jha bha Ñ
     ∷ gh ∷ ḍh ∷ dh ∷ Mṣ                                  -- 9  gha ḍha dha Ṣ
     ∷ j ∷ b ∷ g ∷ ḍ ∷ d ∷ Mś                             -- 10 ja ba ga ḍa da Ś
     ∷ kh ∷ ph ∷ ch ∷ ṭh ∷ th ∷ c ∷ ṭ ∷ t ∷ Mv            -- 11 kha pha cha ṭha tha ca ṭa ta V
     ∷ k ∷ p ∷ My                                         -- 12 ka pa Y
     ∷ ś ∷ ṣ ∷ s ∷ Mr                                     -- 13 śa ṣa sa R
     ∷ h ∷ Ml ∷ []                                        -- 14 ha L

सप्तपञ्चाशत् : length रेखा ≡ 57
सप्तपञ्चाशत् = refl

-- a, the class 8.4.2 itself opens with: a up to the  of stra 5
अट्-आयामः : List Varṇa
अट्-आयामः = a ∷ i ∷ u ∷ Mṇ₁ ∷ ṛ ∷ ḷ ∷ Mk ∷ e ∷ o ∷ Mṅ ∷ ai ∷ au ∷ Mc
          ∷ h ∷ y ∷ v ∷ r ∷ []

अट्-श्रुतिः : klassL a Mṭ रेखा ≡ just अट्-आयामः
अट्-श्रुतिः = refl

अट्-वर्णाः : keep isSound अट्-आयामः
           ≡ a ∷ i ∷ u ∷ ṛ ∷ ḷ ∷ e ∷ o ∷ ai ∷ au ∷ h ∷ y ∷ v ∷ r ∷ []
अट्-वर्णाः = refl

-- śaL: śa of sūtra 13 up to the L of sūtra 14 — crossing the second ha
शल्-आयामः : List Varṇa
शल्-आयामः = ś ∷ ṣ ∷ s ∷ Mr ∷ h ∷ []

शल्-श्रुतिः : klassL ś Ml रेखा ≡ just शल्-आयामः
शल्-श्रुतिः = refl

शल्-वर्णाः : keep isSound शल्-आयामः ≡ ś ∷ ṣ ∷ s ∷ h ∷ []
शल्-वर्णाः = refl

-- yaR: ya of sūtra 5 up to the R of sūtra 13 — between the two ha-s
यर्-आयामः : List Varṇa
यर्-आयामः = y ∷ v ∷ r ∷ Mṭ ∷ l ∷ Mṇ₂ ∷ ñ ∷ m ∷ ṅ ∷ ṇ ∷ n ∷ Mm
          ∷ jh ∷ bh ∷ Mñ ∷ gh ∷ ḍh ∷ dh ∷ Mṣ ∷ j ∷ b ∷ g ∷ ḍ ∷ d ∷ Mś
          ∷ kh ∷ ph ∷ ch ∷ ṭh ∷ th ∷ c ∷ ṭ ∷ t ∷ Mv ∷ k ∷ p ∷ My
          ∷ ś ∷ ṣ ∷ s ∷ []

यर्-श्रुतिः : klassL y Mr रेखा ≡ just यर्-आयामः
यर्-श्रुतिः = refl

यर्-वर्णाः : keep isSound यर्-आयामः
           ≡ y ∷ v ∷ r ∷ l ∷ ñ ∷ m ∷ ṅ ∷ ṇ ∷ n ∷ jh ∷ bh ∷ gh ∷ ḍh ∷ dh
           ∷ j ∷ b ∷ g ∷ ḍ ∷ d ∷ kh ∷ ph ∷ ch ∷ ṭh ∷ th ∷ c ∷ ṭ ∷ t
           ∷ k ∷ p ∷ ś ∷ ṣ ∷ s ∷ []
यर्-वर्णाः = refl

-- the three restrictions to {h y } are the Krama cycle, attested
अट्-हयशेषु : sig₃ (keep tHYŚ अट्-आयामः) ≡ हय-युगम्
अट्-हयशेषु = refl

शल्-हयशेषु : sig₃ (keep tHYŚ शल्-आयामः) ≡ शह-युगम्
शल्-हयशेषु = refl

यर्-हयशेषु : sig₃ (keep tHYŚ यर्-आयामः) ≡ यश-युगम्
यर्-हयशेषु = refl

------------------------------------------------------------------------
-- §6  The impossibility.  Six permutations; for each, no split's middle
--     part has the permutation's outer pair as its {h y ś}-content — and
--     every named class of every once-reciting line IS such a middle
--     part, by §3 + §2.
------------------------------------------------------------------------

षट्क्रमाः : List (List Varṇa)
षट्क्रमाः = (h ∷ y ∷ ś ∷ []) ∷ (h ∷ ś ∷ y ∷ [])
          ∷ (y ∷ h ∷ ś ∷ []) ∷ (y ∷ ś ∷ h ∷ [])
          ∷ (ś ∷ h ∷ y ∷ []) ∷ (ś ∷ y ∷ h ∷ []) ∷ []

-- one seat is denied: the outer pair of a permutation is no middle part
एकासनम् : (Pm : List Varṇa) (pr : Sig₃)
        → eqSig₃ pr pr ≡ true
        → allL (λ tr → not (eqSig₃ (sig₃ (fst (snd tr))) pr)) (allSplits Pm) ≡ true
        → (ℓ₀ q₀ : List Varṇa) (st mk : Varṇa)
        → keep tHYŚ ℓ₀ ≡ Pm
        → klassL st mk ℓ₀ ≡ just q₀
        → sig₃ (keep tHYŚ q₀) ≡ pr
        → ⊥
एकासनम् Pm pr prSelf noOuter ℓ₀ q₀ st mk pP kEq sEq =
  let fac = klassL-factor st mk ℓ₀ q₀ kEq
      us = fst fac
      ws = fst (snd fac)
      kp : keep tHYŚ ℓ₀ ≡ keep tHYŚ us ++ keep tHYŚ q₀ ++ keep tHYŚ ws
      kp = cong (keep tHYŚ) (snd (snd fac)) ∙ keep-++₃ tHYŚ us q₀ ws
      mm : (keep tHYŚ us , (keep tHYŚ q₀ , keep tHYŚ ws)) ∈ᴸ allSplits Pm
      mm = subst (λ zs → (keep tHYŚ us , (keep tHYŚ q₀ , keep tHYŚ ws)) ∈ᴸ allSplits zs)
                 (sym kp ∙ pP)
                 (allSplits-complete (keep tHYŚ us) (keep tHYŚ q₀) (keep tHYŚ ws))
      lk : not (eqSig₃ (sig₃ (keep tHYŚ q₀)) pr) ≡ true
      lk = ∈ᴸ-lookup (λ tr → not (eqSig₃ (sig₃ (fst (snd tr))) pr)) (allSplits Pm) mm noOuter
      fl : not (eqSig₃ (sig₃ (keep tHYŚ q₀)) pr) ≡ false
      fl = cong (λ zs → not (eqSig₃ zs pr)) sEq ∙ cong not prSelf
  in ⊥rec (true≢false (sym lk ∙ fl))

-- THE THEOREM.  h, y,  each recited once (the {h y }-subsequence is one
-- of the six orders): no three classes restrict to the three pairs.  The
-- three sig₃-hypotheses are exactly अट्-हयशेषु, शल्-हयशेषु, यर्-हयशेषु —
-- so a line naming classes with the attested restrictions is refuted.
एकश्रुतौ-त्रयम्-असाध्यम् :
    (ℓ₀ : List Varṇa)
  → keep tHYŚ ℓ₀ ∈ᴸ षट्क्रमाः
  → (st₁ mk₁ st₂ mk₂ st₃ mk₃ : Varṇa) (q₁ q₂ q₃ : List Varṇa)
  → klassL st₁ mk₁ ℓ₀ ≡ just q₁ → sig₃ (keep tHYŚ q₁) ≡ हय-युगम्
  → klassL st₂ mk₂ ℓ₀ ≡ just q₂ → sig₃ (keep tHYŚ q₂) ≡ शह-युगम्
  → klassL st₃ mk₃ ℓ₀ ≡ just q₃ → sig₃ (keep tHYŚ q₃) ≡ यश-युगम्
  → ⊥
एकश्रुतौ-त्रयम्-असाध्यम् ℓ₀ (inl pP) st₁ mk₁ st₂ mk₂ st₃ mk₃ q₁ q₂ q₃ k₁ g₁ k₂ g₂ k₃ g₃ =
  एकासनम् (h ∷ y ∷ ś ∷ []) शह-युगम् refl refl ℓ₀ q₂ st₂ mk₂ pP k₂ g₂
एकश्रुतौ-त्रयम्-असाध्यम् ℓ₀ (inr (inl pP)) st₁ mk₁ st₂ mk₂ st₃ mk₃ q₁ q₂ q₃ k₁ g₁ k₂ g₂ k₃ g₃ =
  एकासनम् (h ∷ ś ∷ y ∷ []) हय-युगम् refl refl ℓ₀ q₁ st₁ mk₁ pP k₁ g₁
एकश्रुतौ-त्रयम्-असाध्यम् ℓ₀ (inr (inr (inl pP))) st₁ mk₁ st₂ mk₂ st₃ mk₃ q₁ q₂ q₃ k₁ g₁ k₂ g₂ k₃ g₃ =
  एकासनम् (y ∷ h ∷ ś ∷ []) यश-युगम् refl refl ℓ₀ q₃ st₃ mk₃ pP k₃ g₃
एकश्रुतौ-त्रयम्-असाध्यम् ℓ₀ (inr (inr (inr (inl pP)))) st₁ mk₁ st₂ mk₂ st₃ mk₃ q₁ q₂ q₃ k₁ g₁ k₂ g₂ k₃ g₃ =
  एकासनम् (y ∷ ś ∷ h ∷ []) हय-युगम् refl refl ℓ₀ q₁ st₁ mk₁ pP k₁ g₁
एकश्रुतौ-त्रयम्-असाध्यम् ℓ₀ (inr (inr (inr (inr (inl pP))))) st₁ mk₁ st₂ mk₂ st₃ mk₃ q₁ q₂ q₃ k₁ g₁ k₂ g₂ k₃ g₃ =
  एकासनम् (ś ∷ h ∷ y ∷ []) यश-युगम् refl refl ℓ₀ q₃ st₃ mk₃ pP k₃ g₃
एकश्रुतौ-त्रयम्-असाध्यम् ℓ₀ (inr (inr (inr (inr (inr (inl pP)))))) st₁ mk₁ st₂ mk₂ st₃ mk₃ q₁ q₂ q₃ k₁ g₁ k₂ g₂ k₃ g₃ =
  एकासनम् (ś ∷ y ∷ h ∷ []) शह-युगम् refl refl ℓ₀ q₂ st₂ mk₂ pP k₂ g₂
एकश्रुतौ-त्रयम्-असाध्यम् ℓ₀ (inr (inr (inr (inr (inr (inr ())))))) st₁ mk₁ st₂ mk₂ st₃ mk₃ q₁ q₂ q₃ k₁ g₁ k₂ g₂ k₃ g₃

------------------------------------------------------------------------
-- §7  And the real line stands outside the hypothesis — as it must.
------------------------------------------------------------------------

हयशाः-रेखायाम् : keep tHYŚ रेखा ≡ h ∷ y ∷ ś ∷ h ∷ []
हयशाः-रेखायाम् = refl

private
  len4≢len3 : {xs : List Varṇa} → length xs ≡ 4 → length xs ≡ 3 → ⊥
  len4≢len3 p₄ p₃ = snotz (injSuc (injSuc (injSuc (sym p₄ ∙ p₃))))

  outside : (Pm : List Varṇa) → length Pm ≡ 3 → keep tHYŚ रेखा ≡ Pm → ⊥
  outside Pm l₃ pP = len4≢len3 {xs = Pm} (sym (cong length pP) ∙ refl) l₃

रेखा-न-एकश्रुतिः : keep tHYŚ रेखा ∈ᴸ षट्क्रमाः → ⊥
रेखा-न-एकश्रुतिः (inl pP) = outside _ refl pP
रेखा-न-एकश्रुतिः (inr (inl pP)) = outside _ refl pP
रेखा-न-एकश्रुतिः (inr (inr (inl pP))) = outside _ refl pP
रेखा-न-एकश्रुतिः (inr (inr (inr (inl pP)))) = outside _ refl pP
रेखा-न-एकश्रुतिः (inr (inr (inr (inr (inl pP))))) = outside _ refl pP
रेखा-न-एकश्रुतिः (inr (inr (inr (inr (inr (inl pP)))))) = outside _ refl pP
रेखा-न-एकश्रुतिः (inr (inr (inr (inr (inr (inr ()))))))

------------------------------------------------------------------------
-- §8  Minimality.  §6 proved repetition count zero
--     impossible for the trio.  Here: the real line's repetition count is
--     exactly ONE — ha twice, every other sound once.  Zero impossible,
--     one attained: in the repetition dimension, for this trio, the
--     Mhevara line is minimal.  (For the full attested family the
--     attainment side rests on the Haskell decision procedure's reading
--     of all ~30 classes, which is not kernel-checked; the NECESSITY side
--     needs only the trio and is §6.  The doubled marker-letter A is a
--     different doubling — two occurrences of an it, priced in
--     `TheSecondNaIsTheCollision` — and is not counted here, where the
--     count is of SOUNDS.)
------------------------------------------------------------------------

गणना : Varṇa → List Varṇa → ℕ
गणना tg []        = zero
गणना tg (x₀ ∷ xs) = if eqV x₀ tg then suc (गणना tg xs) else गणना tg xs

eqℕ : ℕ → ℕ → Bool
eqℕ zero     zero     = true
eqℕ zero     (suc _)  = false
eqℕ (suc _)  zero     = false
eqℕ (suc m₀) (suc n₀) = eqℕ m₀ n₀

वर्णाः : List Varṇa
वर्णाः = a ∷ i ∷ u ∷ ṛ ∷ ḷ ∷ e ∷ o ∷ ai ∷ au
       ∷ h ∷ y ∷ v ∷ r ∷ l ∷ ñ ∷ m ∷ ṅ ∷ ṇ ∷ n
       ∷ jh ∷ bh ∷ gh ∷ ḍh ∷ dh ∷ j ∷ b ∷ g ∷ ḍ ∷ d
       ∷ kh ∷ ph ∷ ch ∷ ṭh ∷ th ∷ c ∷ ṭ ∷ t ∷ k ∷ p ∷ ś ∷ ṣ ∷ s ∷ []

द्विचत्वारिंशत् : length वर्णाः ≡ 42
द्विचत्वारिंशत् = refl

-- ha stands twice in the line; every one of the other forty-one sounds
-- stands exactly once.  One computation over the whole inventory.
एकावृत्तिः : allL (λ v₀ → eqℕ (गणना v₀ रेखा) (if eqV v₀ h then 2 else 1)) वर्णाः
           ≡ true
एकावृत्तिः = refl

-- and the fourteen it-occurrences each stand once, so the line has no
-- hidden doubling anywhere else
अनुबन्धाः-सकृत् : allL (λ v₀ → eqℕ (गणना v₀ रेखा) 1)
                       (Mṇ₁ ∷ Mk ∷ Mṅ ∷ Mc ∷ Mṭ ∷ Mṇ₂ ∷ Mm ∷ Mñ ∷ Mṣ ∷ Mś ∷ Mv ∷ My ∷ Mr ∷ Ml ∷ [])
                ≡ true
अनुबन्धाः-सकृत् = refl

------------------------------------------------------------------------
-- THE CHOICE OF HA WAS NOT ONE.
-- `Niyama_The-
-- DoubledSoundCouldHaveBeenAnyOfThreeAndTheFullClassesRestrictItToHa-
-- Alone.agda` (absent from this repository) proves the trio also restricts to 3-cycles on {h v } and
-- on {h y } (by refl, from this file's own stretches), and proves the
-- impossibility parametrically over any triple.  Case on the doubled
-- sound: ya-doubling dies on {h v }, a-doubling on {h y }, anything
-- else on {h y ś}; only ha survives — aṬ ∩ śaL = {h} exactly, the sole
-- articulation point, checked over the whole inventory.  Within single-
-- doubling lines, ha is forced, not chosen.
------------------------------------------------------------------------
