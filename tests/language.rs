/// Runs on a large stack, as the binary does: recursion and deep values use it.
fn run(src: &str) -> Result<String, String> {
    let src = src.to_string();
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            let mut out = Vec::new();
            tohu::run_source(&src, &mut out).map_err(|e| e.to_string())?;
            Ok(String::from_utf8(out).unwrap())
        })
        .unwrap()
        .join()
        .unwrap()
}

fn example(name: &str) -> String {
    std::fs::read_to_string(format!("{}/examples/{}", env!("CARGO_MANIFEST_DIR"), name)).unwrap()
}

#[test]
fn signs_come_only_from_fermions() {
    let out = run(&example("signs.tohu")).unwrap();
    assert_eq!(
        out,
        "-inl ()\n2·inl () - 2·inr ()\ntohu\n-(psi, psi)\npsi\ninl () + inr ()\ninl () - inr ()\n\
         2·inl () + 2·inr ()\ntohu\ninl () |-> inl () - inr ()\ninr () |-> -inl () + inr ()\n"
    );
}

#[test]
fn laplacian_is_a_four_history_loop() {
    let out = run(&example("laplacian.tohu")).unwrap();
    assert_eq!(
        out,
        "inl 4 - 2·inl 5 + inl 6\n-2·inl 0 + inl 1 + inr 0\n\
         inl 3 - 4·inl 4 + 6·inl 5 - 4·inl 6 + inl 7\ninl 0 - 5·inl 4 + 4·inl 5\n"
    );
}

#[test]
fn iteration_terminates_by_cancellation() {
    let out = run(&example("interference.tohu")).unwrap();
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(&lines[..2], ["()", "()"]);
    assert!(lines[6].starts_with("refuted: overflow"));
    assert_eq!(lines[7], "2·()");
}

#[test]
fn koszul_homology_computes_gcd() {
    let out = run(&example("homology.tohu")).unwrap();
    let h: Vec<&str> = out.lines().filter(|l| l.starts_with("H = ")).collect();
    assert_eq!(
        h,
        [
            "H = [0, Z/2, Z]",
            "H = Z/2 ⊕ ΠZ/2",
            "H = Z/5 ⊕ ΠZ/5",
            "H = 0",
            "H = (Z/6)^2 ⊕ Π(Z/6)^2"
        ]
    );
    assert!(out.contains("inl () |-> tohu\ninr psi |-> (inl (), psi)\n"));
}

#[test]
fn rejected_examples_fail_with_reasons() {
    for (file, needle) in [
        ("association.tohu", "no association"),
        ("clone.tohu", "can be copied"),
        ("forget.tohu", "can be forgotten"),
        ("infinite-trace.tohu", "needs a finite type"),
        ("minus.tohu", "no minus sign"),
        ("not-a-complex.tohu", "not a complex"),
        ("scalar.tohu", "no scalars"),
        ("undetermined.tohu", "its dimension is the answer"),
    ] {
        let err = run(&example(&format!("rejected/{}", file))).unwrap_err();
        assert!(err.contains(needle), "{}: {}", file, err);
    }
}

#[test]
fn adjoint_of_composite_reverses_order() {
    let src = "type Nat = mu n. 1 + n; type Int = Nat + Nat;
        def succ : Int <-> Int = (id + unfold) ; assocl+ ; ((swap+ ; fold) + id);
        expect ~(succ ; succ ; succ) (inl 1) => inr 1;
        expect ~succ (inl 0) => inr 0;";
    assert_eq!(run(src).unwrap(), "");
}

#[test]
fn koszul_sign_on_exchange() {
    let src = "def x : (1 + Psi) * Psi <-> Psi * (1 + Psi) = swap*;
        run x (inl (), psi) + 2·(inr psi, psi);";
    assert_eq!(run(src).unwrap(), "(psi, inl ()) - 2·(psi, inr psi)\n");
}

#[test]
fn trace_over_psi_matches_cup_and_cap() {
    // loop[Psi] f equals the bent wire with one exchange, for a non-trivial f.
    let src = "type Bool = 1 + 1; type Fermi = 1 + Psi;
        def f : Fermi * Psi <-> Fermi * Psi = distl ; (id + swap*) ; factorl;
        def traced : Fermi <-> Fermi = loop[Psi] f;
        def bent : Fermi <-> Fermi =
          unitir* ; (id * cup) ; assocl* ; (f * id) ; assocr* ; (id * (swap* ; cap)) ; uniter*;
        run traced (inl ()) + inr psi;
        run bent (inl ()) + inr psi;";
    let out = run(src).unwrap();
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines[0], lines[1]);
}

#[test]
fn opposite_parities_only_meet_in_tohu() {
    // The only map from an even line to an odd one is zero.
    let src = "type Fermi = 1 + Psi;
        def z : 1 <-> Psi = loop[Fermi]
          (unitel* ; (cup + unitir*) ; swap+ ; (swap* + swap*) ; factorl ; swap*);
        table z;";
    assert_eq!(run(src).unwrap(), "() |-> tohu\n");
}

#[test]
fn expectation_failure_is_reported() {
    let src = "type Bool = 1 + 1; def two : Bool <-> Bool = loop[Bool] id; expect two (inl ()) => inl ();";
    assert!(run(src).unwrap_err().contains("expectation failed"));
}

#[test]
fn deep_recursion_runs() {
    let src = "type Nat = mu n. 1 + n; type Int = Nat + Nat;
        def succ : Int <-> Int = (id + unfold) ; assocl+ ; ((swap+ ; fold) + id);
        def add : Nat * Int <-> Nat * Int =
          (unfold * id) ; distl ; (id + (add ; (id * succ))) ; factorl ; (fold * id);
        expect add (2000, inl 0) => (2000, inl 2000);";
    assert_eq!(run(src).unwrap(), "");
}

#[test]
fn arithmetic_and_exchange() {
    let out = run(&example("arithmetic.tohu")).unwrap();
    assert_eq!(
        out,
        "(3, inl 8)\n(3, inl 2)\n(7, 2)\n(inl 55, inl 89)\n(inl 0, inl 1)\n\
         -([psi, psi, psi], [psi])\n([psi, psi], [psi])\n"
    );
}
