sig Addr {}
sig Data {}

sig Mem {
	addrs : set Addr,
	map : addrs -> lone Data
	}{
	addrs in map.Data  // "map tiene todas las memorias de addrs, con o sin datos"
}

sig MainMem extends Mem {}

sig Cache extends Mem {
	mugre: set addrs
}//"set addrs" se entiende como un subconjunto de direcciones de la memoria principal.

sig System {
	cache: Cache,
	main: MainMem
	}{
	cache.addrs in main.addrs   // toda dirección de cache existe en mainMem
}

pred Read [s, s':System, a:Addr, d:Data] {
	// Dirección hallada en caché:
	(a in s.cache.addrs implies
		(s' = s and (let d'= s.cache.map[a] | some d' implies d = d')))
	// Dirección hallada en memoria principal:
	(((not (a in s.cache.addrs)) and a in s.main.addrs) implies
		(s'.main.map = s.main.map and s'.cache.mugre = s.cache.mugre and
		 (let d' = s.main.map[a] |
			some d' =>
				// Tenía un dato mapeado:
				(d = d' and s'.cache.map = s.cache.map ++ (a->d))
			else
				// No tenía dato :
				(s'.cache.map = s.cache.map)
	)))
	// Dirección inexistente:	
	((not (a in (s.cache.addrs + s.main.addrs))) implies  s = s')
}

pred Readaux [s, s':System, a:Addr, d:Data] {
	Read [s, s', a, d]
	not s.cache = s'.cache
}

pred Write [s,s':System, a:Addr, d:Data]{
	// La dirección está en caché:

}

pred Writeaux [s, s':System, a:Addr, d:Data]{
	Write [s, s', a, d]
	a in (s.cache.addrs + s.main.addrs)
}

pred Flush [s,s':System]{
	s'.cache = s.cache
	s'.main.addrs = 
}

//run Readaux for 3 but exactly 2 System
//run Writeaux for 4 but exactly 2 System
