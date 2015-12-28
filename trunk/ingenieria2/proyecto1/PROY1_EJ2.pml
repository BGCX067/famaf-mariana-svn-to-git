#define m 25
int n = 7;
bool max[7];
int a[7];
int result = 0;

/* Banderas: */
int done = 0;
	int maxready = 0;
bool loaded = false;
int check_done = 0;
bool mostrado = false;
bool verificado = false;

/* Para verificar propiedades ltl: */
bool finished = false;
bool correct = true;

active proctype FAST_MAX (){
	int k;
	int i;
	int j;

	/* Inicializa el arreglo de booleanos: */
	for (k:0..n-1) {
		run INITBOOL(k);
	}

	/* Llena el arreglo de enteros de manera no determinística: */
	maxready == n;
	run load();

	/* Corre el algoritmo de verificación de manera paralela: */
	loaded == true;
	for (i:0..n-1){
		for (j:0..n-1){
			run INPARALLEL (i,j);
		}
	}
	done == n*n;

	for (i:0..n-1){
		run PARALLEL_CHECK (i);
	}

	/* Muestra el arreglo y el resultado: */
	check_done == n;
	run MOSTRAR ();

	mostrado == true;
	run VERIFY();
	
	verificado == true;
	finished = true;
}

proctype INITBOOL (int i){
	max[i] = true;
	maxready++;
}

proctype VERIFY(){
	int i;
	done == n*n;
	for (i:0..n-1){
		correct = correct && a[i]<=result;
	}
	verificado = true;
}

proctype MOSTRAR (){
	int i;

	for (i:0..n-1){
		printf ("a en %d: %d\n", i, a[i]);
	}
	printf ("resultado: %d\n", result);
	mostrado = true;
}

proctype INPARALLEL(int i,j){
	if
	:: a[i] < a[j] -> max[i] = false;
	:: else /*No hace cosa alguna.*/
	fi;
	done++;
}

proctype PARALLEL_CHECK (int i){
	if 
	:: max[i] -> result = a[i];
	:: else -> skip;
	fi;
	check_done++;
}

proctype load(){
	int i;
	int j;
	for (i in a) {
		j = 0;
		do
		:: (j<m) -> a[i]++ ; j++;
		:: (j<m) -> a[i]-- ; j++;
		:: else  -> break;
		od;
	}
	loaded = true;
}
/* Comentar las siguientes líneas en caso de no usar iSpin, o alguna de las propiedades en caso de usarlo: */
ltl  correcto  {
	[] (correct == true);
}

/*ltl termina {
	<> (finished == true);
}*/
