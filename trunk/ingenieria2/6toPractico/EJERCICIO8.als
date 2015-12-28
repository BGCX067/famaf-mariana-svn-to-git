--Tomando como ejemplo el "Cruce del río" dado en clase.
-- No anda
open util/ordering[Estado]

------------------------------------------------------------------------------------------------------------------
//Dominio del problema:
abstract sig Alguien {golpea: set Alguien}

one sig Policia, Papa, Mama, Ladron, nene1, nene2, nena1, nena2 extends Alguien {}

fact golpes {
	golpea = Papa->(nene1 + nene2) 
				+ Mama->(nena1 + nena2)
				+ Ladron->(Alguien-Policia-Ladron)
}

------------------------------------------------------------------------------------------------------------------
//Estados:
sig Estado {
	cerca: set Alguien,
	lejos: set Alguien,
	yate: Int
}

//Estado inicial:
fact estInicial {
	let s0 = first[] | s0.cerca = Alguien && no s0.lejos
}

pred resuelto []{
	last[].lejos = Alguien
}

------------------------------------------------------------------------------------------------------------------
//Cruce del río:
pred cruzar [desde, desde', hacia, hacia': set Alguien]{
	some p, p':Alguien |
		(p' in Policia + Mama + Papa &&
		desde' = desde - p -p' &&
		hacia' = hacia +p +p')
}

fact cruce {
	all s:Estado, s':next[s] | (
		s.yate = 0 => cruzar[s.cerca, s'.cerca, s.lejos, s'.lejos] &&
		s.yate = 1 => cruzar [s.lejos, s'.lejos, s.cerca, s'.cerca])
	all s:Estado, p:Alguien | (p in s.cerca <=> p!in s.lejos)
	all s:Estado |
		(Mama in s.cerca && Papa !in s.cerca => Mama.golpea !in s.cerca &&
		Papa in s.cerca && Mama !in s.cerca => Papa.golpea !in s.cerca &&
		Ladron in s.cerca && Policia !in s.cerca => Ladron.golpea !in s.cerca &&
		Mama in s.lejos && Papa !in s.lejos => Mama.golpea !in s.lejos &&
		Papa in s.lejos && Mama !in s.lejos => Papa.golpea !in s.lejos &&
		Ladron in s.lejos && Policia !in s.lejos => Ladron.golpea !in s.lejos)
}

run resuelto for 30 Estado
