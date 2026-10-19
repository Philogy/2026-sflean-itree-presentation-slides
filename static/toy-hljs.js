// highlight.js grammar for the toy language and its semantics sketches,
// so every keyword (`while`, `do`, `if`, `then`, ...) gets the same colour.
RevealHighlight().hljs.registerLanguage('toy', hljs => ({
  keywords: {
    keyword: 'skip let in if then else while do store deref alloc print read ' +
             'def inductive abbrev fun match with',
    type: 'Nat Stmt State Trace Prop Cfg Option Event Oracle Error Program',
    literal: 'none some true false ub outOfFuel invalidVar'
  },
  contains: [
    hljs.COMMENT('--', '$'),
    hljs.C_NUMBER_MODE
  ]
}));
