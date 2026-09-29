import P10

/-! MUST FAIL (M34): a certificate proving a *different* proposition (the unpacked
`Underdetermined` statement, without the byte binding) is not accepted for `Holds`. -/
set_option maxRecDepth 100000
example : P10.Bound (filebytes% "vectors/p1.instance.json") (hex% "62353069823aace3a91b37ffabcdf7b2d608134457276b2a5e597ebb49e0e824") := P10.Certs.P1.underdetermined
