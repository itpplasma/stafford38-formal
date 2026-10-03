module
public import Lean

@[expose] public section

open Lean
open Lean.Elab.Command

namespace DependencyClosureCore

private structure Issue where
  name : Name
  owner : Option Name
  kind : String
  detail : String
  path : Array Name
  deriving Inhabited, Repr

private structure Report where
  root : Name
  visited : Nat
  requiredReached : Array Name
  forbidden : Array Issue
  incomplete : Array Issue
  deriving Inhabited, Repr

private meta def moduleOf? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  some env.header.moduleNames[idx.toNat]!

private meta def dependencyPath (root : Name) (parent : Std.HashMap Name Name) (target : Name) : Array Name := Id.run do
  let mut path := #[target]
  let mut current := target
  let mut steps := 0
  while current != root && steps <= parent.size do
    if let some p := parent[current]? then
      path := path.push p
      current := p
      steps := steps + 1
    else
      break
  return path.reverse

private meta def isStructural (ci : ConstantInfo) : Bool :=
  match ci with
  | .inductInfo _ | .ctorInfo _ | .recInfo _ | .quotInfo _ => true
  | _ => false

private meta def inspectRoot
    (env : Environment)
    (root : Name)
    (bannedOwners bannedNames requiredNames allowedAxioms : Array Name) : Report := Id.run do
  let mut todo : Array Name := #[root]
  let mut seen : Std.HashSet Name := {}
  let mut parent : Std.HashMap Name Name := {}
  let mut forbidden : Array Issue := #[]
  let mut incomplete : Array Issue := #[]
  let mut requiredReached : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if !seen.contains n then
      seen := seen.insert n
      if requiredNames.contains n then
        requiredReached := requiredReached.push n
      let owner? := moduleOf? env n
      if bannedNames.contains n then
        forbidden := forbidden.push ⟨n, owner?, "forbidden", "named forbidden producer", dependencyPath root parent n⟩
      match owner? with
      | some owner =>
        if bannedOwners.contains owner then
          forbidden := forbidden.push ⟨n, owner?, "forbidden", s!"declaration belongs to forbidden module {owner}", dependencyPath root parent n⟩
      | none =>
        incomplete := incomplete.push ⟨n, none, "module_owner_missing", "no loaded module owner is available", dependencyPath root parent n⟩
      match env.find? n with
      | none =>
        incomplete := incomplete.push ⟨n, owner?, "constant_missing", "referenced constant is absent from the loaded environment", dependencyPath root parent n⟩
      | some ci =>
        let mut deps := ci.type.getUsedConstants
        match ci.value? (allowOpaque := true) with
        | some value =>
          deps := deps ++ value.getUsedConstants
        | none =>
          if isStructural ci then
            pure ()
          else
            match ci with
            | .axiomInfo _ =>
              if !allowedAxioms.contains n then
                incomplete := incomplete.push ⟨n, owner?, "body_unavailable", "bodyless axiom is not on the explicit standard-axiom allowlist", dependencyPath root parent n⟩
            | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
              incomplete := incomplete.push ⟨n, owner?, "body_unavailable", "definition/theorem/opaque body unavailable in the loaded module environment", dependencyPath root parent n⟩
            | .quotInfo _ | .inductInfo _ | .ctorInfo _ | .recInfo _ => pure ()
        for d in deps do
          if !seen.contains d then
            if parent[d]?.isNone then
              parent := parent.insert d n
            todo := todo.push d
  return ⟨root, seen.size, requiredReached, forbidden, incomplete⟩

private meta def standardAxioms : Array Name := #[`propext, `Quot.sound, `Classical.choice]

private meta def emitReport (report : Report) : CommandElabM Unit := do
  logInfo m!"root: {report.root}; declarations reached: {report.visited}; forbidden hits: {report.forbidden.size}; unavailable dependencies: {report.incomplete.size}"
  if !report.requiredReached.isEmpty then
    logInfo m!"required declarations reached: {report.requiredReached}"
  for issue in report.forbidden do
    logInfo m!"forbidden dependency path (terminal to producer): {issue.path}; declaration={issue.name}; {issue.detail}"
  for issue in report.incomplete do
    logInfo m!"incomplete dependency path: {issue.path}; declaration={issue.name}; {issue.detail}"
    logInfo m!"STAFFORD_DEPENDENCY_GUARD_INCOMPLETE\t{report.root}\t{issue.name}\t{issue.owner.getD `none}\t{issue.kind}"

syntax (name := auditFixtureDeps) "#auditDependencyClosure " ident " forbidden " ident : command

elab_rules : command
  | `(#auditDependencyClosure $root:ident forbidden $producer:ident) => do
    let report := inspectRoot (← getEnv) root.getId #[] #[producer.getId] #[] standardAxioms
    emitReport report
    unless report.forbidden.isEmpty && report.incomplete.isEmpty do
      throwError m!"fixture dependency closure rejected for {root.getId}"

syntax (name := auditDependencyRoute) "#auditDependencyRoute " ident " required " ident " forbidden " ident : command

elab_rules : command
  | `(#auditDependencyRoute $root:ident required $requiredDecl:ident forbidden $producer:ident) => do
    let report := inspectRoot (← getEnv) root.getId #[] #[producer.getId] #[requiredDecl.getId] standardAxioms
    emitReport report
    unless report.incomplete.isEmpty do
      throwError m!"route dependency inspection was incomplete for {root.getId}"
    unless report.forbidden.isEmpty do
      throwError m!"route dependency inspection reached forbidden endpoint {producer.getId}"
    unless report.requiredReached.contains requiredDecl.getId do
      throwError m!"route dependency inspection did not reach required endpoint {requiredDecl.getId}"
    logInfo m!"dependency route passed: {root.getId} reaches {requiredDecl.getId} and excludes {producer.getId}"

syntax (name := auditStaffordTerminalDeps) "#auditStaffordTerminalDeps" : command

elab_rules : command
  | `(#auditStaffordTerminalDeps) => do
    let env ← getEnv
    let targets : Array Name := #[
      `Stafford38.universalStatement,
      `Stafford38Challenge.universalStatement,
      `Stafford38.universalFixedSourceStatement,
      `Stafford38FixedSourceChallenge.universalFixedSourceStatement]
    let oldOwner := `Stafford38.Geometry.GeneralAsymptoticLaurentAxis
    let bannedNames : Array Name := #[
      `Stafford38.Geometry.GeneralConormalAxis.exists_groundConormalAxis_of_minimalPrime_unit_transcendental,
      `Stafford38.Geometry.CanonicalNonconstantFiniteGradientProductionProof.exists_groundConormalAxis_of_regularizedOneRowConormalData,
      `Stafford38.Geometry.CanonicalVisibleDivisorFrameProduction.exists_finiteGradientBoundaryCertificateOver_of_hasVisibleDivisorFrame,
      `Stafford38.Geometry.CanonicalNonconstantFiniteGradientProductionProof.finiteGradientBoundaryCertificateOver_of_regularizedOneRowConormalData,
      `Stafford38.Geometry.FiniteGradientResidueExtension.exists_groundConormalAxis_of_finiteGradientBoundaryCertificateOver]
    let allowOld := (← IO.getEnv "STAFFORD_ALLOW_OLD_ROUTE") == some "1"
    let mut strictFailures : Array String := #[]
    let mut incompleteFailures : Array String := #[]
    for root in targets do
      let report := inspectRoot env root #[oldOwner] bannedNames #[] standardAxioms
      emitReport report
      if !report.incomplete.isEmpty then
        incompleteFailures := incompleteFailures.push s!"{root}: {report.incomplete.size} unavailable dependencies"
      if !report.forbidden.isEmpty then
        strictFailures := strictFailures.push s!"{root}: {report.forbidden.size} forbidden producer dependencies"
    if !incompleteFailures.isEmpty then
      throwError m!"strict dependency guard could not inspect all bodies/references: {incompleteFailures}"
    if strictFailures.isEmpty then
      logInfo m!"strict dependency guard passed for all {targets.size} terminal roots"
    else if allowOld then
      logWarning m!"explicit --allow-old-route diagnostic mode; strict guard would fail: {strictFailures}"
    else
      throwError m!"strict dependency guard rejected old producer dependencies: {strictFailures}"

end DependencyClosureCore
