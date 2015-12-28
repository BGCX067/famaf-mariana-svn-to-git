sig Interprete {}
sig Cancion {}

sig Catalogo{
	canciones: set Cancion,
	interpretes: set Interprete,
	interpretaciones: canciones->interpretes
}{
	/*all c:Cancion | c in canciones =>
		(some i:Interprete | i in interpretes and
			c = interpretaciones.i)
	all i:Interprete | i in interpretes =>
		(some c:Cancion | c in canciones and
			i = interpretaciones[c])*/
	interpretaciones.interpretes = canciones
	canciones.interpretaciones = interpretes
}

pred show [c:Catalogo] {
}

pred AgregarInterpretacion [c, c':Catalogo, t:Cancion, i:Interprete]{
		c'.interpretaciones = c.interpretaciones + (t->i)
} 

pred aux [c, c':Catalogo, t:Cancion, i:Interprete]{
	t->i in c.interpretaciones
	QuitarInterpretacion [c, c', t, i]
	c != c'
}

pred funaux [c:Catalogo]{
	some InterpreteCopion[c]
}

pred QuitarInterpretacion [c,c':Catalogo, t:Cancion, i:Interprete]{
		c'.interpretaciones = c.interpretaciones - t->i
}

fun InterpreteCopion [c:Catalogo] : Interprete->Interprete {
	((~(c.interpretaciones)).(c.interpretaciones)) - (iden)
}
//run show for 7 but exactly 1 Catalogo
//run AgregarInterpretacion  for 7 but exactly 2 Catalogo
//run aux  for 5 but exactly 2 Catalogo
//run QuitarInterpretacion for 7 but exactly 2 Catalogo
//run InterpreteCopion for 7 but exactly 1 Catalogo
run funaux  for 5 but exactly 1 Catalogo
