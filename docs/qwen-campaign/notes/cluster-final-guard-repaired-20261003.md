# Final replay after dependency inspection repair

This driver preserves the reviewed fresh public-checkout verifier, exact source
identity and executable modes, pinned Lean and all ten dependency revisions,
full library/consumer checks, and all four actual Palomar comparisons. It is
used only after the actual failed terminal dependency guard has been repaired
and its strict production and independent fixture checks have passed.

The changes from the original replay driver are bounded to distinct fresh
source/receipt paths, the accepted isolated Bubblewrap 0.12.0 PATH entry, and
reuse of the completed allocation's existing compiled cache through a logged
symlink. The donor cache must be a real directory contained beneath the run
root; the prior guard must have finished without a stop cause or surviving
children. Only one guarded allocation writes the cache. Lake source traces,
source identity and dependency pins are still checked.

Luna reviewed the driver delta and requested the donor symlink/containment
checks; the controller added them. Bash syntax checking passed. The driver
accepts an exact forty-hex public source commit as its argument. Preparation
is not a successful replay receipt. No resource cap or verification gate is
changed. Preserve both earlier failed final-run archives.

Driver SHA-256: `1b861f175547cb8e0073aa636af9bfd54f481d56c2b59e0ee0bfb77467a7f838`.
