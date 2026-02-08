(lang dune 3.14)
(name garter)

(generate_opam_files true)

(using menhir 3.0)

(package
 (name garter)
 (synopsis "Garter programming language compiler")
 (depends
  (ocaml (>= 5.0))
  (cmdliner (>= 1.2))
  (ounit2 :with-test)
  (extlib (>= 1.7))
  (menhir (>= 20230608))))
