import P10

/-! MUST FAIL: the certificate of P1 is reused for the bytes of `n2_incompatible`
(stale certificate / changed component): the checker-owned proposition differs. -/
set_option maxRecDepth 100000
example : P10.Bound (filebytes% "vectors/negative/n2_incompatible.json") (hex% "62353069823aace3a91b37ffabcdf7b2d608134457276b2a5e597ebb49e0e824") := P10.Certs.P1.cert
