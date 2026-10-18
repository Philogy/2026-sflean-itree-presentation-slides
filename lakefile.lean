import Lake

open Lake DSL

require «verso-slides» from git "https://github.com/leanprover/verso-slides.git"@"v4.36.0-rc1"

package «sflean-itree-presentation» where
  version := v!"0.1.0"

lean_lib Talk
lean_lib Defs

@[default_target] lean_exe slides where root := `Main
