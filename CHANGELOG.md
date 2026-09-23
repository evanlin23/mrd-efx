# Changelog

* **v1.2.0** — certificates for every theorem named in the paper's appendix (54 audited statements);
  `MRDBridge.additive_via_monotone_L` (the bridge for the paper's Algorithm 2); `MRD.mrdLA`, an
  array-backed executable of the paper's algorithm proved equal to `mrdL`; the audit script computes
  its expected count and rejects the word `sorry` in sources; the test driver runs `mrdLA` with a
  shape check and exits nonzero on failure; documentation and CI refresh.
* **v1.1.0** — always-last-agent variant (`mrdL`, `mrdML`); 40 audited statements.
* **v1.0.0** — initial release: greedy-then-dump algorithm, monotone extension, bridge, degree-3
  sharpness example; 35 audited statements.
