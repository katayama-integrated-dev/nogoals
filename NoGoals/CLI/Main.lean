import NoGoals.IR.Atoms
import NoGoals.IR.Assets
import NoGoals.IR.HtmlRaw
import NoGoals.IR.HtmlVerified
import NoGoals.Resolve.Refine
import NoGoals.Render.Plan
import NoGoals.Render.Html
import NoGoals.Verify.Permalinks

namespace NoGoals.CLI

open NoGoals
open System (FilePath)

/-! ## Asset Loading

Binary-safe file operations for loading assets (images, fonts, etc.)
-/

/-- Load a file as binary data (images, fonts, PDFs, etc.)
    This correctly handles non-UTF8 files unlike IO.FS.readFile. -/
def loadBinaryFile (path : FilePath) : IO ByteArray :=
  IO.FS.readBinFile path

/-- Load multiple asset files from disk into a function suitable for Assets.bytes.
    Returns a function that maps each index to the corresponding file's bytes.

    Example usage:
    ```
    let assetPaths := #["./assets/images/logo.png", "./assets/images/hero.jpg"]
    let assetBytes ← loadAssetBytes assetPaths
    let assets : Assets 2 := {
      name := ...
      kind := ...
      bytes := assetBytes
      unique := ...
    }
    ```
-/
def loadAssetBytes {n : Nat} (paths : Array FilePath) (_h : paths.size = n := by native_decide) :
    IO (Fin n → ByteArray) := do
  let mut bytes : Array ByteArray := #[]
  for path in paths do
    let data ← loadBinaryFile path
    bytes := bytes.push data
  let finalBytes := bytes
  pure fun i =>
    let idx := i.val
    if h' : idx < finalBytes.size then
      finalBytes[idx]
    else
      ByteArray.empty  -- Should never happen if paths.size = n

/-- Load a single asset file, returning ByteArray.
    Useful for building assets one at a time. -/
def loadAsset (path : FilePath) : IO ByteArray :=
  loadBinaryFile path

/-- Check if a file exists and is readable -/
def assetExists (path : FilePath) : IO Bool :=
  try
    let _ ← IO.FS.readBinFile path
    pure true
  catch _ =>
    pure false

/-- Write a single file to disk -/
def writeFile (outputDir : FilePath) (file : File) : IO Unit := do
  -- Strip leading slash from path to make it relative
  let pathStr := file.path.toString
  let relativePath := if pathStr.startsWith "/" then (pathStr.drop 1).toString else pathStr
  if !NoGoals.Verify.Permalinks.pathContained relativePath then
    throw (IO.userError s!"output path escapes the output root: {file.path.toString}")
  let fullPath := outputDir / relativePath
  -- Create parent directories if needed
  let parentDir := fullPath.parent.getD outputDir
  IO.FS.createDirAll parentDir
  -- Write the file (binary write for ByteArray)
  IO.FS.writeBinFile fullPath file.bytes
  IO.println s!"  ✓ {relativePath}"

/-- Write all files from a build plan to disk -/
def writeBuildPlan (outputDir : FilePath) (plan : BuildPlan) : IO Unit := do
  IO.println s!"Writing {plan.files.length} files to {outputDir}..."
  for file in plan.files do
    writeFile outputDir file
  IO.println s!"✅ Build complete! {plan.files.length} files written."

/-- Generate a site from a build plan -/
def generateSite (outputDir : String) (plan : BuildPlan) : IO UInt32 := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  NoGoals - Formally Verified Static Site Generator"
  IO.println "  The smallest SSG that cannot emit a broken website"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  -- Create output directory
  let outPath : FilePath := outputDir
  IO.FS.createDirAll outPath

  -- Write all files
  writeBuildPlan outPath plan

  IO.println ""
  IO.println s!"🎉 Site generated successfully in: {outputDir}"
  pure 0

/-- Main CLI entry point. NoGoals is a library; sites drive it from their own
    build executable (see my-site's `build-site`, whose `--audit`
    mode runs the full publisher gate suite). -/
def run : IO UInt32 := do
  IO.println "NoGoals — the smallest static site generator that cannot emit a broken website"
  IO.println ""
  IO.println "NoGoals is a Lean library, driven by the consuming site's build executable."
  IO.println "From a consuming site (e.g. my-site):"
  IO.println "  lake exe build-site                 build the site (fail-closed)"
  IO.println "  lake exe build-site --audit         build + full publisher gate suite"
  IO.println "In this repo:"
  IO.println "  lake build && lake script run test  proofs + tests + axiom audit"
  IO.println "  ./verify.sh                         recompute every public claim"
  pure 0

end NoGoals.CLI
