typedef struct s_nodo *nodo;

typedef struct s_Lado *Lado;

typedef struct s_List *List;

struct listnod{
	nodo a[MAX];
	int num;
};

struct s_nodo{
	int name;
	int color;
	u32 flujo;
	u32 capacidad;
	bool saturado;
	bool marcado;
	bool coloreado;
};

struct s_Lado{
	int padre;
	nodo hijos[MAX];
	int num_hijos;
};

struct s_List{
	Lado lados[MAX];
	int num_lados;
	
};

