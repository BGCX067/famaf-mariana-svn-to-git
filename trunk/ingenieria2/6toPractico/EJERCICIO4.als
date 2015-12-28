sig Node {}
sig Grafo {
	arista: Node->Node
}

pred aciclico [g:Grafo]{
	no (iden & ^(g.arista))
}

pred noDirigido [g:Grafo]{
	~(g.arista) = g.arista
}

pred fconexo [g:Grafo]{
	*(g.arista)= g.arista
}//No encuentra instancias

pred conexo [g:Grafo]{
	*(~(g.arista) + g.arista) = g.arista
}//No encuentra instancias	

//run aciclico for 7 but exactly 1 Grafo
//run noDirigido for 7 but exactly 1 Grafo
run conexo for 7 but exactly 1 Grafo
