// 3.9 Keywords
<YYINITIAL> {
  // 3.9 Keyword
  "typestate"                    { return sym(Terminals.TYPESTATE); }
  "end"                          { return sym(Terminals.END); }
  "enum"                         { return sym(Terminals.ENUM); }
}
