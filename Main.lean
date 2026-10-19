module
import VersoSlides
import Talk
import Defs

open VersoSlides

-- Look and post-processing adapted from leodemoura/ETAPSTutorial2026.

def titleSlide : String :=
  "<section class=\"title-slide split\" data-state=\"title\">" ++
  "<div class=\"logo-pane\"><img class=\"logo\" src=\"itree-logo.svg\" alt=\"ITree\"></div>" ++
  s!"<div class=\"text-pane\"><h1>{Title}</h1>" ++
  "<div class=\"meta\"><strong>Philippe Dumonet</strong></div>" ++
  "<div class=\"date\">SF Lean | 2026</div>" ++
  "</div></section>"

def icon (name : String) : IO String := do
  let svg ← IO.FS.readFile ("static" / s!"{name}.svg")
  return svg.trimAscii.toString.replace "<svg " "<svg class=\"icon\" fill=\"currentColor\" aria-hidden=\"true\" "

def outroSlide : IO String := do
  let row (ic text : String) (href : Option String := none) : IO String := do
    let body := s!"{← icon ic}<span>{text}</span>"
    return match href with
      | some h => s!"<a class=\"contact\" href=\"{h}\">{body}</a>"
      | none => s!"<div class=\"contact\">{body}</div>"
  return "<section class=\"title-slide split outro\" data-state=\"title\">" ++
    "<div class=\"logo-pane\"><img class=\"logo\" src=\"itree-logo.svg\" alt=\"ITree\"></div>" ++
    "<div class=\"text-pane\"><h1>Thanks for listening!</h1><div class=\"contacts\">" ++
    (← row "mail" "philippe@dumo.net" (some "mailto:philippe@dumo.net")) ++
    (← row "x" "@real_philogy" (some "https://x.com/real_philogy")) ++
    (← row "github"  "slides: Philogy/2026-sflean-itree-presentation-slides"
      (some "https://github.com/Philogy/2026-sflean-itree-presentation-slides")) ++
    "</div></div></section>"

def slideHeader : String :=
  "<div class=\"slide-header\"></div>"

public def main : IO UInt32 := do
  let config : Config := { theme := "white", slideNumber := true, transition := "fade", center := false, margin := 0 }
  let rc ← slidesMain (config := config) (doc := %doc Talk)
  let out := config.outputDir
  IO.FS.writeFile (out / "custom.css") (← IO.FS.readFile ("static" / "custom.css"))
  IO.FS.writeFile (out / "itree-logo.svg") (← IO.FS.readFile ("static" / "itree-logo.svg"))
  let htmlPath := out / "index.html"
  let html ← IO.FS.readFile htmlPath
  -- custom.css must come after the bundled stylesheets, which `extraCss` doesn't guarantee.
  let html := html.replace "</head>" "<link rel=\"stylesheet\" href=\"custom.css\"></head>"
  -- custom.css sizes slides with vh/vw, so reveal.js must not scale them.
  let html := html.replace "Reveal.initialize({" "Reveal.initialize({\n        disableLayout: true,"
  -- Registered before `Reveal.initialize`, which runs the highlight plugin.
  let html := html.replace "Reveal.initialize({" ((← IO.FS.readFile ("static" / "toy-hljs.js")) ++ "Reveal.initialize({")
  -- Slides with attributes (e.g. a background colour) are left without the header.
  let html := html.replace "<section>" s!"<section>{slideHeader}"
  let html := html.replace "<div class=\"slides\">" s!"<div class=\"slides\">{titleSlide}"
  let html := html.replace "</section></div>" s!"</section>{← outroSlide}</div>"
  IO.FS.writeFile htmlPath html
  -- Inline the hover docs: `fetch` fails when the deck is opened from `file://`.
  let docs ← IO.FS.readFile (out / "-verso-docs.json")
  for js in ["highlighting.js", "panel.js"] do
    let path := out / "lib" / js
    let src ← IO.FS.readFile path
    IO.FS.writeFile path (src.replace "fetch(\"-verso-docs.json\")" s!"Promise.resolve(\{ ok: true, json: () => ({docs}) })")
  return rc
