import VersoSlides
import Talk

open VersoSlides

def main : IO UInt32 :=
  slidesMain
    (config := { theme := "white", slideNumber := true, transition := "slide" })
    (doc := %doc Talk)
