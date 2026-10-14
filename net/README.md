# net: optimal reduction by interaction

The substrate `NET_SPEC.md` §7 asks for: duplication and substitution under
binders by Lamping / Asperti–Guerrini, with a binder as its body subnet
(`LAM(x,t) ⋈ APP(r,a) → x = a, t = r`) and sharing through levelled fans
(`DUP_k(SUP_k(a,b)) → (a,b)`), as in the binder correction recorded in
`MACHINE_SPEC.md`.

`net.c` transcribes, rule by rule, from:

- Asperti & Guerrini, *The Optimal Implementation of Functional Programming
  Languages*, pp. 40–42 (rules and initial encoding), as stated in
  Salikhmetov, *Token-passing Optimal Reduction with Embedded Read-back*,
  EPTCS 225 (2016) §4, and as carried by codedot/lambda
  `encoding/standard/{index.js,template.txt}`;
- read-back: the same paper §7 and the same template.

One rule is added and marked ADDED in the source: a bracket or croissant
meeting an application whose head is a variable passes into its fields.

Input: the codedot/lambda syntax (`x, y: body`, application by
juxtaposition, `name = term;` definitions, `#` comments). Each definition
used is bound once and shared through fans.

Output: the normal form, and its length, the number of interactions (5.6).
Interactions that exist only because read-back put an atom in a binder are
counted separately (5.21).

Check, when the owner permits running: the number of β-interactions is
Lévy's count of redex families, so it must equal the `B` column of
codedot/lambda's benchmark table on the same terms (e.g. 7 for `w2eta`, 14
for `counter`).

Not yet built on this substrate: the cubical layer (interval and faces,
systems, comp and its head table, Glue, ua) and the identity agents of
`NET_SPEC.md` §§1–5.
