sig Node {
}

sig System {
	link: Node ->Node,
	channel : Node -> one Int
}{
	link = ~link 
	no (link & iden) 
	all n: Node | n.channel > 0 && n.channel < 15
}

/* SpecSystem es un sistema que solo puede usar los canales 1,6 y 11 */
sig SpecSystem extends System {} {
	all n: Node | n.channel = 1 or n.channel = 6 or n.channel = 11 
}

pred NonConflicting [s:System, n:Node] {
	all n':Node | n in s.link[n'] => s.channel[n] != s.channel[n']
}

pred NodesNonConflicting [s:System, ns: set Node ]{
	ns = s.link[Node] & {n:Node | NonConflicting [s, n]}
}

pred SpecReconfig [s, s': SpecSystem] {
	#(s.link) > 5
	all n: Node | s.link[n] = s'.link[n]
	all n: Node | not NonConflicting[s, n] 
	all n: Node | NonConflicting [s', n]
}

pred Reconfig [s, s': System, cn: set Node] {
	#(s.link) > 5
	all n: Node | s.link[n] = s'.link[n]
	all n: Node | (n not in cn) implies s.channel[n] = s'.channel[n]
	all n: Node | not NonConflicting[s, n] 
	all n: Node | (n in cn) implies NonConflicting [s', n]
}

// Para conseguir un sistema irresoluble
pred Unsolvable [s: System, cn: set Node] {
	#(s.link[Node]) > 15
	some n1:Node | all n2: Node | (n2 != n1 implies (n1 -> n2) in s.link) and cn = n1
	# (s.channel[Node]) = 14
}

// Para conseguir un sistema especial irresoluble
pred UnsolvableSpec [s: SpecSystem] {
	# s.link[Node] > 4
	s.link = (Node<: univ->univ :> Node) - iden
}

//Reconfig para un System sin solución:
pred ReconfigUnsolvable [s,s':System, cn:set Node]{
	Unsolvable [s, cn]
	#(s.link) > 5
	all n: Node | s.link[n] = s'.link[n]
	all n: Node | (n not in cn) implies s.channel[n] = s'.channel[n]
	all n: Node | not NonConflicting[s, n] 
	all n: Node | (n in cn) implies NonConflicting [s', n]
}

//Reconfig para un SpecSystem sin solución:
pred ReconfigUnsolvableSpec[s,s':SpecSystem]{
	#(s.link) > 5
	some sin: SpecSystem | UnsolvableSpec[sin]	
	all n: Node | s.link[n] = s'.link[n]
	all n: Node | not NonConflicting[s, n] 
	all n: Node | NonConflicting [s', n]
}
//run NonConflicting for 30 but exactly 1 System, 6 Int
//run UnsolvableSpec for 30 but 1 System, 6 Int

//INCISO 1
//run NodesNonConflicting for 30 but exactly 1 System, 6 Int

//INCISO 2
//run Reconfig for 30 but exactly 2 System, 5 Int

//INCISO 3
//run SpecReconfig for 30 but exactly 2 SpecSystem, 5 Int

//SISTEMAS SIN SOLUCIÓN: (no debería encontrar instancias)
//run ReconfigUnsolvable for 30 but exactly 2 System, 5 Int
run ReconfigUnsolvableSpec for 30 but exactly 2 System, 5 Int
