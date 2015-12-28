open util/ordering [Estado]

/* -------  Signaturas ------- */

abstract sig Gente {
	golpea: set Gente,
	protege: Gente -> Gente}
one sig mama, papa, ladron, policia, nena1, nena2, nene1, nene2 extends Gente {}
fact golpes {
	golpea = mama -> (nene1 + nene2)
				+ papa -> (nena1 + nena2)
				+ ladron -> (Gente - ladron- policia)
}

fact proteccion {
	protege = mama -> (nena1 + nena2) -> papa
				+ papa -> (nene1 + nene2) -> mama
				+ policia -> (Gente - ladron - policia) -> ladron
}

/* -------  Estados: ------- */
sig Estado {
	cerca: set Gente,
	lejos: set Gente,
	barco: Int
}

fact estadoInicial {
	let s0 = first[] | s0.cerca = Gente && no s0.lejos
}

pred estadoFinal [] {
	last[].lejos = Gente && no last[].cerca
}

/* -------  Cruce del río: ------- */
pred cruzar [desde, desde', hacia, hacia': set Gente]{
	some p, p':Gente |
		p in (policia + mama + papa) &&
		desde' = desde - p - p' &&
		hacia' = hacia + p +p'
}

fact cruceCorrecto {
	all s:Estado, s':next[s] |
		s.barco = 0 => cruzar[s.cerca, s'.cerca, s.lejos, s'.lejos] &&
		s.barco = 1 => cruzar[s.lejos, s'.lejos, s.cerca, s'.cerca] &&
		all p:Gente | (
			(p in s'.cerca && some t:Gente | t in p.golpea & s'.cerca => (some p':Gente | t in  (p'.protege).p && p' in s'.cerca))
			&& (p in s'.lejos && some t:Gente | t in p.golpea & s'.lejos => (some p':Gente | t in  (p'.protege).p && p' in s'.lejos))
			&& (p in s'.lejos <=> p !in s'.cerca)
			)
}

run estadoFinal for 30 Estado
