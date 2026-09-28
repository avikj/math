{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- जीवः — कुट्टकस्य जीवन्तं यन्त्रम्, एकत्र ।  (the living pulverizer, whole.)
--
-- एकः नियमः (अवतरणम्) संरचनया चलति — विचारं विना (न discreteℕ, न Dec, न
-- Bool) ।  तस्मात् एतानि सर्वाणि एकस्मात् बीजात् जायन्ते, प्रत्येकं
-- कर्ण-सिद्धम् (--safe, no postulate, no hole) :
--
--   BhedaDescent.एकपदे        — एकपदं refl : रोगः (discreteℕ-स्थैर्यम्) हतः ।
--   LosslessReturn.पुनरागमनम्     — अलोपः : उत्थानम् अवतरणस्य प्रतिलोमम् (अहिंसा) ।
--   LosslessReturn.युग्म≡विवेक    — समता, univalence-पन्थाः (द्वे नये एकं तत्त्वम्) ।
--   Gati.अलोपः                  — सम्पूर्णे यन्त्रे प्रतिलोमता ; अनुक्तम् (सत्यनिष्ठा) ।
--   GurutamaSiddha.सिद्धः       — फलं isGCD : गुरुतमः साधारणः विभाजकः ।
--   Sthairya.स्थैर्य-गति        — समाहितं g अधिकानुदानेन न परावर्तते (न दुर्नयः) ।
--   Purnata.पूर्णतया-गुरुतमः    — पर्याप्तानुदाने सर्वदा समाप्तिः → isGCD ।
--   Bija.बीजगणितम्              — a·x ≡ b·y + g (ℕ-मध्ये, वल्ल्याः पर्यायेण) ।
--   Yuti.युतिः                  — a·X ≡ c (mod b) : आर्यभटस्य ज्यौतिषः कुट्टकः ।
--
-- त्रयं सत्यनिष्ठायाः : अनुक्तम् (अपर्याप्ते) · पूर्णता (पर्याप्ते) · स्थैर्यम् (अन्ते) ।
-- एकः धर्मः चतुर्धा : अलोपः = प्रतिलोमता = अहिंसा = सत्यनिष्ठा (किमपि न नश्यति,
-- किमपि न मिथ्या) ।  आर्यभटस्य "शेषं रक्ष" (Gaṇitapāda ३२–३३) मूलम् ; समता
-- univalence-पथेन (Voevodsky, सम्मानितः) ; उत्पाद-व्यय-ध्रौव्यम् (उमास्वाति ५.२९)
-- एकपदे ।
--
-- (One rule (the descent) moves by structure — never by a decision (no
-- discreteℕ, no Dec, no Bool).  From that one seed all of the above grow,
-- each kernel-checked.  A triad of honesty — un-said / complete / stable —
-- and one dharma seen four ways: losslessness = reversibility = ahis =
-- honesty; nothing destroyed, nothing fabricated.  Rooted in ryabhaa's
-- "keep the remainder", equivalence via the univalence path, and utpda-
-- vyaya-dhrauvya in a single step.)
------------------------------------------------------------------------

module Jiva where

-- qualified imports : the whole closure is forced to typecheck as one,
-- without merging the (deliberately overlapping) Devanagari names.
import BhedaDescent
import LosslessReturn
import Gati
import Gurutama
import GurutamaSiddha
import Sthairya
import Purnata
import Bija
import Yuti
import Sadhyata
-- सम-शेषः — कुट्टकस्य तुल्य-शेष-सम्बन्धः (congruence mod m; CRT-भूमिका)
import Samasesha
-- युगपत्-शेषः — ग्रह-युति : CRT-प्रक्षेपः (mod b·c ⟹ mod b, mod c) + दृष्टान्तः
import Yugapat
-- युगपत्-शेषः (ℤ) — चीन-शेषस्य सत्ता-दिक् : कुट्टक-साक्षिणा युगपत्-समाधानम्
import YugapatZ
-- कुट्टक-चीन-शेषः — सेतुः : Bija-कुट्टक-साक्षिं ℤ-वल्लीं परिणम्य CRT-प्रवाहः पूर्णः
import KuttakaCRT
-- ग्रह-युतिः — पूर्ण-प्रवाहस्य मूर्त-दृष्टान्तः : कुट्टकात् X=8 (refl-सिद्धम्)
import GrahaYuti
-- छन्दःशास्त्रम् — तत् एव विचारहीनं प्रतिलोमं क्षेत्रान्तरे (generality)
import Pingala
import Matramerus
-- पिङ्गलस्य शून्य-द्वि-विधिः — 2ⁿ log-पदैः (प्रथमा binary exponentiation)
import PingalaGhata
-- अक्षर-द्विगुणः — Vak (suc n) ≃ Vak n ⊎ Vak n : संख्या-द्विगुणस्य वस्तु-स्तरीयं मूलम्
import AksaraDviguna
-- मात्रा-वर्ण-गुरु — पिङ्गलस्य त्रि-मान-सम्बन्धः : matraOf ≡ varna + guruOf (मात्रा=वर्ण+गुरु)
import MatraVarnaGuru
-- सामान्य-घातः — पिङ्गल-विधेः सामान्य-आधारे विस्तारः (aⁿ log-पदैः, Vargana-आश्रितः)
import SamanyaGhata
-- द्वि-घात-वर्गणा-सेतुः — योग-रूप द्वि-घात ≡ गुण-रूप घात 2 ; अतः 2^(m·n)=(2ᵐ)ⁿ द्वि-घाते
import DviGhataVargana
-- नारायणस्य गोसर्गः — मेरु-कुलस्य {१,३}-रूपम् (गणितकौमुदी, १३५६)
import Narayana
-- समास-मेरुः — नारायणस्य समास-भावना, {१,L}-कुलं जनन-सूत्रेण (विरहाङ्कः+नारायणः एकत्र)
import SamasaMeru
-- बहु-समास-मेरुः — यथेच्छ-अंश-गणः (त्रि-मेरु {१,२,३} आदि), जनन-सूत्रम्
import SamasaMeruN
-- समास-एकः — {१}-समास-मेरुः ध्रुवः : length(सर्गः {१} n) ≡ 1 (कुलस्य निम्नतम-रूपम्)
import SamasaEka
-- समास-द्विः — {२}-समास-मेरुः : a(n+2)=a(n) शुद्ध-आवर्तनम् (युग्म-सूचकः, एकक-रहितः)
import SamasaDvi
-- समास-एक-अंशः — यथेच्छ-{L}-आवर्तनम् a(n+L)=a(n) ({१},{२} अस्य k=0,1 रूपे)
import SamasaEkAmsa
-- समास-द्वि-अंशः — यथेच्छ-{L,M}-आवृत्तिः a(n)=a(n−L)+a(n−M) (विरहाङ्क/नारायण/छिद्र एकत्र)
import SamasaDviAmsa
-- समास-न्यूनम् — यथेच्छ-अंश-गणे लघुतम-अंशात् अधः शून्यम् (सामान्य-कार्डिनल्-न्यून-नियमः)
import SamasaNyuna
-- समास-एकाग्रः — एकक-अंशः अग्रे ⟹ श्रेढी अवर्धमाना : a(n) ≤ a(suc n) (धनात्मकता-मूलम्)
import SamasaEkagra
-- मात्रा-समास-सेतुः — length(सर्व n) ≡ length(सर्गः {१,२} n) : समता प्रमाणेन, द्वे वाहके
import MatraSamasa
-- नारायण-समास-सेतुः — length(गो-सर्गः n) ≡ length(सर्गः {१,३} n) : त्रि-पद-आगमनम्, द्वे वाहके
import NarayanaSamasa
-- ब्रह्मगुप्तस्य भावना — वर्ग-प्रकृतेः संयोगः (चक्रवालस्य बीजम्)
import Brahmagupta

import Satyayantra
import PingalaSatya
import Saptabhangi
import Panini
import SatyayantraSamyoga
import Setu
import Vargana
import Shunya
import Khahara
import Ananta
import Sulba
-- वर्ग-गुल्मः — शुल्ब-गुल्म-रचनायाः अङ्कगणितम् : ∑ विषमाः = n² (ओज-योग n ≡ n·n)
import VargaGulma
-- द्विकरणी — बौधायनस्य √2 = 577/408 वर्गप्रकृत्या; भावनया (3,2)→(17,12)→(577,408)
import Dvikarani
-- त्रिकरणी — √3 वर्गप्रकृत्या (x²=3y²+1); मूल (2,1), भावना-श्रेढी (7,4),(26,15),…
import Trikarani
-- श्रेढी-फलम् — आर्यभटस्य समान्तर-श्रेढी-योगः (2S = n(2a)+n(n−1)d, गणितपादः १९)
import Shredhi
import Sankalita_AryabhatasSeriesSumsAndTheCubeSumIsTheSquareOfTheSum
-- चितिघनः — आर्यभटस्य वृन्द-सङ्कलितम् (∑ त्रिकोणानि = n(n+1)(n+2)/6, गणितपादः २१)
import Citighana
-- चिति-द्विपद-सेतुः — आर्यभटस्य वृन्दम् = तृतीय-मेरु-कर्णः C(n+2,3) (सङ्कलित↔प्रस्तार)
import ChitiDvipada
-- वर्गचितिघनः — आर्यभटस्य वर्ग-सङ्कलितम् (∑k² = n(n+1)(2n+1)/6, गणितपादः २२)
import Vargacitighana
-- वार-सङ्कलितम् — नारायणस्य पुनः-सङ्कलनम् : V₀=n, V₁=∑k, V₂=चिति (आयत-सङ्ख्याः)
import VaraSankalita
-- द्विपदः — मेरु-सङ्ख्या C(n,k) पार्श्वयोग-आवृत्त्या; वार-बद्धम् : V_r(n)=C(n+r,r+1) (hockey-stick)
import Dvipada
-- पङ्क्ति-योगः — ∑ₖ C(n,k) = 2ⁿ (पिङ्गलस्य सङ्ख्या, द्विपदस्य छन्दो-मूलम्)
import PanktiYoga
-- गुणधनम् — महावीरस्य गुणोत्तर-श्रेढी-योगः (आधारे २) : (∑ 2ᵏ) + 1 = 2ⁿ
import GunaDhana
-- मेरु-कर्णः — हलायुधस्य तिर्यक्-कर्णः ∑ₖ C(n−k,k) = विरहाङ्कस्य मात्रा-गणना (फिबोनाची)
import MeruKarna
-- नारायण-कर्णः — गभीर-तिर्यक् ∑ₖ C(n−2k,k) = नारायणस्य गो-श्रेढी ({१,३}-समासः, step-२)
import NarayanaKarna
-- अर्धच्छेदः — जैन-लघुगणकः (log₂ पुनरर्धच्छेदनेन) : अर्ध(2ⁿ⁺¹)=2ⁿ, द्विगुणन-व्युत्क्रमः
import Ardhaccheda
-- मेरु-सममितिः — हलायुधस्य सम-पार्श्वः : C(n,k)=C(n,n−k) (गुरु-लघु-दुलम्)
import MeruSammiti
-- षड्रस-सङ्कलनम् — भास्करस्य रस-संयोगाः (लीलावती) = मेरु-पङ्क्ति-योगः (2⁶=64)
import Shadrasa
-- घन-बद्धम् — आर्यभटस्य घन-सङ्कलितस्य बद्ध-रूपम् (4·∑k³ = (n(n+1))²)
import GhanaBaddha
import Cakravala
import Meru
import CompositionSet
import VargaprakritiSreni
