(lang dune 3.16)
(using coq 0.7)
(name coq-egraph)

(source (github ericwang385/coq-egraph))
(bug_reports "https://github.com/ericwang385/coq-egraph/issues")

(generate_opam_files true)

(package
 (name coq-shell)
 (synopsis "A formalized model of the EGraph.")
 (version 0.1)
 (depends
  (coq (>= 8.17))))
