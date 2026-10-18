// highlight.js grammar for the toy language and its semantics sketches,
// so every keyword (`while`, `do`, `if`, `then`, ...) gets the same colour.
RevealHighlight().hljs.registerLanguage('toy', hljs => ({
  keywords: {
    keyword: 'skip let in if then else while do store deref ref print read ' +
             'def inductive abbrev fun match with',
    type: 'Nat Stmt State Trace Result Prop Cfg Option Event',
    literal: 'none some true false outOfFuel'
  },
  contains: [
    hljs.COMMENT('--', '$'),
    hljs.C_NUMBER_MODE
  ]
}));
