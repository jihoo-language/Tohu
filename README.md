# Tohu

*Tohu wa-bohu*: formless and void.

[ASL](https://github.com/jihoo-language/asl) is hard because of what you have to know. [Aporia](https://github.com/jihoo-language/aporia) is hard because of what it takes away: names, copying, forgetting and exchange. Tohu keeps Aporia's restrictions, lets the mathematics back in, and changes what a program *is*. A Tohu program is no longer a bijection that picks one history. It is a ℤ-linear map that **counts** histories, and some histories count −1.

| In Aporia | In Tohu |
| --- | --- |
| a value is one value | a run takes and returns **integer combinations** of values, such as `inl 4 - 2·inl 5 + inl 6` |
| a time loop needs exactly one consistent history | a time loop is a **supertrace**. All consistent histories are added, and a history that sends back an odd value counts −1 |
| a paradox is an error | a paradox is the zero vector, printed `tohu` |
| a bootstrap (two pasts) is an error | a bootstrap counts its pasts. With one even and one odd past, it annihilates |
| there is no exchange | `swap*` exists, but exchanging two odd values costs −1 |
| `~f` runs `f` backward | `~f` is the **adjoint** (transpose) of `f`. Most terms have no inverse |
| `iter` runs until it leaves | `iter` runs until **no history is left circulating**. Histories can cancel each other and end a run that would otherwise go on forever |
| the output is a value | the output can also be the **integer homology** of a complex you built, computed by Smith normal form |

Tohu has no minus sign and no scalars. The number −1 is the dimension of a fermion. The number 6 is the dimension of `(1 + 1) * (1 + (1 + 1))`. Every coefficient you see in an output was produced by counting consistent histories.

## Run a program

```sh
nix run path:. -- examples/homology.tohu
```

```text
H = [0, Z/2, Z]
...
H = Z/2 ⊕ ΠZ/2
H = Z/5 ⊕ ΠZ/5
H = 0
H = (Z/6)^2 ⊕ Π(Z/6)^2
```

The first line is the homology of the real projective plane. The others come from fermions on two or three sites. Each of these complexes computes the greatest common divisor of its weights. [Homology example](examples/homology.tohu)

For development, use the flake's shell:

```sh
nix develop -c cargo test
printf '%s\n' 'type Bool = 1 + 1; def neg : Bool <-> Bool = loop[Psi] id; run neg (inl ());' | nix develop -c cargo run -q -- -
```

## Types

| Type | Basis vectors | Parity |
| --- | --- | --- |
| `0` | none | |
| `1` | `()` | even |
| `Psi` | `psi` | **odd** |
| `A + B` | `inl a`, `inr b` | that of `a` or `b` |
| `A * B` | `(a, b)`. Nest the pairs explicitly. | sum of the parities |
| `mu x. T` | `fold t` | that of `t` |

A type denotes the free abelian group on its values. The parity of a value is the number of `psi` it contains, modulo two. The **dimension** of a finite type is its number of even values minus its number of odd values. So `Psi` has dimension −1, `1 + Psi` has dimension 0 and `Psi * Psi` has dimension 1.

As in Aporia, `A + B + C` and `A * B * C` are errors. A type of the shape `mu x. 1 + x` prints numerals, and `mu x. 1 + A * x` prints lists.

## Terms

A term `f : A <-> B` denotes a ℤ-linear map that preserves parity. There is no application and no lambda.

| Term | Type | On a basis vector |
| --- | --- | --- |
| `id` | `A <-> A` | |
| `swap+` | `A + B <-> B + A` | |
| `swap*` | `A * B <-> B * A` | `(a, b)` ↦ `(b, a)`, negated when **both** are odd |
| `assocl+`, `assocr+`, `unite+`, `uniti+` | as in Aporia | |
| `assocl*`, `assocr*`, `unitel*`, `unitil*`, `uniter*`, `unitir*` | as in Aporia | |
| `distl`, `factorl` | `(A + B) * C <-> (A * C) + (B * C)`, and back | only the left factor can be inspected |
| `annl`, `annil`, `annr`, `annir` | `0 * A <-> 0` and so on | |
| `cup`, `cap` | `1 <-> Psi * Psi`, and back | the self-duality of the fermion |
| `fold`, `unfold` | `T[mu x. T / x] <-> mu x. T`, and back | |
| `f ; g` | composition, `f` first | |
| `f + g`, `f * g` | on each summand, or on each factor | |
| `~f` | `B <-> A` | the transpose of `f` |
| `loop[U] f` | `A <-> B` for `f : A * U <-> B * U`, `U` finite | the supertrace over `U` |
| `iter f` | `A <-> B` for `f : A + U <-> B + U` | the execution formula |

Every primitive is a parity-preserving permutation of basis vectors, sometimes with a sign. The only sign comes from `swap*`. Everything else is a consequence of the two traces.

```text
def name : A <-> B = term;
run term combination;                  // print the output
expect term combination => combination;
refute term combination;               // the run must fail; print why
table term;                            // the image of every basis vector
homology f1, f2, ..., fk;              // homology of a complex
```

A combination is `tohu`, or a signed sum of terms such as `2·(inl ())`, `-inr 3` and `(psi, psi)`. You can write `*` instead of `·`.

## Loops count histories

On input `a`, `loop[U] f` tries every basis value `u` of `U` and runs `f(a, u)`. Each output term `(b, u)` that sends back the value it received is a consistent history and contributes `b`. It contributes `-b` when `u` is odd. So `loop[U] id` is multiplication by the dimension of `U`:

```text
def neg  : Bool <-> Bool = loop[Psi] id;         // -inl ()
def two  : Bool <-> Bool = loop[Bool] id;        // 2·inl ()
def void : Bool <-> Bool = loop[1 + Psi] id;     // tohu
def grandfather : Bool <-> Bool = loop (id * not);  // tohu
```

The sign on odd histories is forced. Exchanging two fermions costs −1, so for yanking (`loop swap* = id`) to hold on `Psi`, a fermion sent back in time must cost −1 as well. It also makes `loop[Psi] f` equal the bent wire made from `cup`, one `swap*` and `cap`, and the tests check that equation.

A superposition is a loop with two histories. Make the feedback choose between two maps, and the loop adds them. With feedback `1 + Psi` instead of `1 + 1`, the loop subtracts them:

```text
def both : Bool <-> Bool = loop[Bool]  (swap* ; distl ; ((id * id) + (id * not)) ; factorl ; swap*);
def diff : Bool <-> Bool = loop[Fermi] (swap* ; distl ; ((id * id) + (id * not)) ; factorl ; swap*);
run both ; diff (inl ());    // tohu, because (1 - X)(1 + X) = 1 - X² = 0
```

The feedback is the right factor, and only the left factor can be inspected. So it is exchanged to the left first, which is free because every value of `Bool` is even. [Signs example](examples/signs.tohu)

### The Laplacian

The discrete Laplacian on the integers needs four histories. Two even ones step right and left. Two odd ones stay where they are, and each counts −1.

```text
type Walk = Bool + (Psi + Psi);
def lap : Int <-> Int =
  loop[Walk] (swap* ; distl
    ; ((distl ; ((id * succ) + (id * ~succ)) ; factorl) + id)
    ; factorl ; swap*);
run lap ; lap (inl 5);   // inl 3 - 4·inl 4 + 6·inl 5 - 4·inl 6 + inl 7
```

The Laplacian is self-adjoint, so `~lap` is `lap`. [Laplacian example](examples/laplacian.tohu)

## A matrix entry is a Lefschetz number

The hard part of writing Tohu is getting a **zero** where you want one. A sum of permutation matrices cannot send one basis vector to zero and another to a basis vector, because modulo two every column sums to the number of terms. The trace of a permutation counts its fixed points, and that count can differ from input to input.

The annihilator of a fermion sends `psi` to `psi` moved into a tag on the right, and sends the empty site to `tohu`:

```text
type Site = 1 + Psi;
type Tag  = Site * Psi;
def pair : Site <-> Tag = (cup + unitil*) ; swap+ ; factorl;
def rot  : Three <-> Three = assocl+ ; swap+;     // no fixed point
def flip : Three <-> Three = id + swap+;          // one fixed point
def ann : Site <-> Tag =
  loop[Three] (distl ; ((id * rot) + (id * flip)) ; factorl ; (pair * id));
```

```text
inl () |-> tohu
inr psi |-> (inl (), psi)
```

The permutation `pair` needs `cup`, because the empty site has to be matched with an even value of `Tag`, and every even value there contains two fermions. A brute-force search over all signed permutations shows that **three feedback values are the minimum**. No loop around a signed permutation with one or two feedback values gives `ann`, whatever the parities of those values, while every feedback with three values works.

## Homology

`homology f1, ..., fk;` takes a complex `C0 -> C1 -> ... -> Ck` of finite types. It checks that each composite of consecutive maps is `tohu` on every basis vector, and prints the homology at each object in order. Every map preserves parity, so each group splits into an even part and an odd part. The odd part is marked `Π`, the parity shift. The real projective plane takes two lines:

```text
def twice : 1 <-> 1 = loop[Bool] id;
def never : 1 <-> 1 = loop[Fermi] id;
homology twice, never;     // H = [0, Z/2, Z]
```

A single term `d : C <-> C * Psi` is read as an **odd** differential. Its fermion carries the change of parity, `d ; (d * id)` must vanish, and the output is `ker d / im d`.

### Fermions compute the gcd

Put fermions on `n` sites and let `d` remove one of them, from site `i` with weight `wᵢ`, and carry it to the far right. Moving it past every occupied site to its right costs a sign through `swap*`. These are the signs that make the boundary square to zero. You never write them down; you choose an order of factors, and the Koszul rule does the rest.

```text
def d_4_6 : F2 <-> F2 * Psi =
  loop[Bool] (swap* ; distl
    ; ((id * ((ann4 * id) ; assocr* ; (id * swap*) ; assocl*))
       + (id * ((id * ann6) ; assocl*)))
    ; factorl ; swap*);
homology d_4_6;            // H = Z/2 ⊕ ΠZ/2
```

This is the Koszul complex of the weights on the exterior algebra. Its homology is $(\mathbb Z/g)^{2^{n-1}}$, where $g = \gcd(w_1,\dots,w_n)$, split evenly between the two parities. The weights 6, 10 and 15 have no coprime pair, yet `homology d_6_10_15` prints `H = 0`. The weights 12, 18 and 30 give `(Z/6)^2 ⊕ Π(Z/6)^2`. [Homology example](examples/homology.tohu)

## Iteration ends by cancellation

`iter f` feeds the `U` part of `f`'s output back into `f` until it is `tohu`. The `B` parts of every pass are added up. Under `iter`, a permutation always returns on a finite type, but a sum need not:

```text
def bose  : Q <-> Q = loop[Bool]  (swap* ; distl ; ((id * g) + (id * h)) ; factorl ; swap*);
def fermi : Q <-> Q = loop[Fermi] (swap* ; distl ; ((id * g) + (id * h)) ; factorl ; swap*);
refute iter bose ();   // the coefficients double on every pass
run iter fermi ();     // 2·()
```

`g` and `h` each return `()` on their own. Their sum never returns. Their difference returns on the third pass, when two histories meet at the same state with opposite signs. [Interference example](examples/interference.tohu)

## Facts

* **Every term preserves parity.** A map between an even line and an odd one is `tohu`.
* **Zero is free, partial zeros are not.** `loop[0] (annr ; annir)` is the zero map between any two types, because a trace over `0` has no histories. A map that is zero on some basis vectors and not on others needs the fixed-point counting above.
* **Without `cup`, fermion number is conserved.** Every other primitive keeps the number of `psi` in a basis vector, and so do both traces. So `cup` cannot be defined from the rest, and `Psi * Psi` would not be isomorphic to `1`.
* **The Euler characteristic constrains the loop.** Let `loop[U] f` have type `C <-> C * Psi` for a signed permutation `f`. Then the Euler characteristic of `C` times the dimension of `U` is 0, because `f` must match the even and odd values of `C * U` with those of `(C * Psi) * U`. So a differential on a complex with nonzero Euler characteristic needs a feedback whose bootstrap annihilates.
* **Aporia's first two open problems become trivial.** Exchange on `Nat * Nat` is `swap*`, and the Fibonacci step is `swap* ; addz`. [Arithmetic example](examples/arithmetic.tohu)

## Rejected programs

Each file in [examples/rejected](examples/rejected) fails with a reason:

```text
error: 2:27: Tohu has no minus sign. The only source of -1 is a fermion: `loop[Psi] id` is minus the identity
error: 2:29: `3` is not a term. Tohu has no scalars; 3 times the identity is a loop whose feedback has dimension 3
error: 2:36: `dup` does not exist: nothing in Tohu can be copied. A linear map cannot copy a superposition, and Tohu has no other kind of map
error: 3:23: a loop takes a trace, and a trace needs a finite type: `Nat` is recursive
error: 3:31: the feedback type of this loop is not determined, and its dimension is the answer; write `loop[U]`
error: 4:16: not a complex: `both` after `both` sends inl () to something other than tohu
```

## Open problems

We do not know the answers to these questions.

1. Without `cup`, is the annihilator `ann` expressible? It conserves fermion number, so the conservation law does not rule it out. A single loop around a `cup`-free permutation cannot give it: `Site` and `Tag` have different numbers of values with each fermion count, so no such permutation of `Site * U` onto `Tag * U` exists unless `U` is `0`.
2. Is there a term of type `Nat <-> Nat * Nat` whose matrix is a permutation matrix, written without recursive definitions? This is Aporia's third problem, which survives here.
3. Is there a term of type `Nat <-> Nat` that sends each `n ≥ 1` to the sum of its divisors as basis vectors, `n ↦ Σ_{d | n} d`?
4. On `n` sites with all weights 1, what is the smallest feedback type of a single loop around a signed permutation that gives the Koszul differential? For `n = 1` it is three values.

## Implementation

The interpreter is written in Rust and uses only the standard library. Type inference is Aporia's unification, extended with `Psi`, `swap*`, `cup` and annotated loops. A vector is a sorted map from values to `i128` coefficients, and overflow is reported, never wrapped. Evaluation takes a direction flag, so `~f` costs nothing. Homology uses the Smith normal form over ℤ. A loop's feedback type may have at most 65,536 basis vectors. `iter` may make two million basis-vector steps, and the support of a vector in it may reach 2²⁰. Recursion has a depth limit of 100,000.
