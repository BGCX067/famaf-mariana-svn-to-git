open util/ordering[Estado]

------------------------------------------------------------------------------------------------------------------
//Dominio del problema:
abstract sig Alguien {}

one sig Policia, Papa, Mama, Ladron, nene1, nene2, nena1, nena2 extends Alguien {}

/*fact golpes {
	golpea = Papa->(nene1+nene2) + Mama->(nena1+nena2) + Ladron->(Alguien-Policia-Ladron)
}*/

------------------------------------------------------------------------------------------------------------------
//Estados:
sig Estado {
	cerca: set Alguien,
	lejos: set Alguien,
}

//Estado inicial:
fact estInicial {
	let s0 = first[] | s0.cerca = Alguien && no s0.lejos
}

//Estado final:
pred resuelto []{
	last[].lejos = Alguien
}

------------------------------------------------------------------------------------------------------------------
//Cruce del río:
pred cruzar [desde, desde', hacia, hacia':set Alguien]{
	some p:Alguien |
		p in (Policia+Mama+Papa) && (desde' = desde-p && hacia' = hacia + p)
	||
	some p, p':Alguien |
		p' in (Policia + Mama + Papa)
		&& desde' = desde - p - p'
		&& hacia' = hacia +p +p'
}

fact transicion {
	all s:Estado, s':next[s] |
		(all p:Alguien |
			p in s.lejos => cruzar[s.lejos, s'.lejos, s.cerca, s'.cerca] &&
			p in s.cerca => cruzar[s.cerca, s'.cerca, s.lejos, s'.lejos] &&
			p in s.cerca <=> p !in s.lejos)
	all s:Estado|
		Mama in s.lejos && (nena1 in s.lejos || nena2 in s.lejos) => Papa in s.lejos &&
		Mama in s.cerca && (nena1 in s.cerca || nena2 in s.cerca) => Papa in s.cerca &&
		Papa in s.lejos && (nene1 in s.lejos || nene2 in s.lejos) => Mama in s.lejos &&
		Papa in s.cerca && (nene1 in s.cerca || nene2 in s.cerca) => Mama in s.cerca &&
		Ladron in s.lejos && some p:Alguien-Ladron | p in s.lejos => Policia in s.lejos &&
		Ladron in s.cerca && some p:Alguien-Ladron| p in s.cerca => Policia in s.cerca &&
		Alguien = (s.cerca + s.lejos)
}

run resuelto for 30 Estado
