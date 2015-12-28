sig Estado {}
sig Etiqueta {}
one sig Tau extends Etiqueta {}
sig lts {
	estados : set Estado,
	ini: Estado,
	aristas: Etiqueta->estados->estados
}{
	estados = ini.*(Etiqueta.aristas)
	
}

pred show [s:lts] {
	some s.aristas
	#estados > 2
}

/*alcanzable: check {
	all l:lts |
		all s:Estado | s in l.estados => s in (l.ini).*(Etiqueta.(l.aristas))
} for 7*/


//INCISO a:
---------------
pred simulacion [sis,sis':lts, rel:Estado->Estado]{
	sis.ini -> sis'.ini in rel
	all s,t:Estado, a:Etiqueta |
		(s->t in rel && s in sis.estados && t in sis'.estados && a in (sis.aristas.Estado.Estado & sis'.aristas.Estado.Estado)&&
		all s':Estado | s' in sis.estados && a->s->s' in sis.aristas => 
			(some t':Estado| t' in sis'.estados && s'->t' in rel && a->t->t' in sis'.aristas))
}

pred aux [s,s':lts, rel:Estado->Estado]{
	s!=s'
	bisimulacion[s,s',rel]
}
//INCISO b:
---------------
pred bisimulacion [s, s': lts, rel:Estado->Estado]{
	simulacion [s,s',rel] && simulacion [s', s, ~rel]
}

//INCISO c:
---------------

//run show for 7 but exactly 1 lts
run aux for 5 but exactly 2 lts
