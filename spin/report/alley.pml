#define ndown	1
#define nup		1

mtype = { mutex_up_t, mutex_down_t, alley_free_t }
mtype = { up_t, down_t }

//The semaphores
short mutex_down 	= 1;
short mutex_up 	= 1;
short alley_free 	= 1;
short up_count 	= 0;
short down_count	= 0;

/*inline V(sema_selector) {
	if
	:: (sema_selector == mutex_down_t) -> mutex_down++;
	:: (sema_selector == mutex_up_t) -> mutex_up++;
	:: (sema_selector == alley_free_t) -> alley_free++;
	:: else -> skip;
	fi
}*/

inline V_down() {
	mutex_down++;
}

inline V_up() {
	mutex_up++;
}

inline V_alley() {
	alley_free++;
}

inline P_down() {
	if
	:: (mutex_down > 0) ->mutex_down--;
	:: else -> skip;
	fi
}

inline P_up() {
	if
	:: (mutex_up > 0) -> 	mutex_up--;
	:: else -> skip;
	fi
}

inline P_alley() {
	if
	:: (alley_free > 0) ->	alley_free--;
	:: else -> skip;
	fi
}

/*
inline P(sema_selector) {
	if
	:: (sema_selector == mutex_down_t 	&& mutex_down > 0) ->mutex_down--;

	:: (sema_selector == mutex_up_t 	&& mutex_up > 0) -> 	mutex_up--;

	:: (sema_selector == alley_free_t 	&& alley_free > 0) ->	alley_free--;
	:: else -> skip;
	fi;
}
*/
inline enter(car_type) {

	if
	:: (car_type == up_t) ->
// reacahes this
//		P(mutex_up_t);
		P_up();

//TODO: skip as else-clause

		up_count++;

		if
		:: (up_count == 1) ->
//			P(alley_free_t);
			P_alley();
		:: else -> skip;
		fi;

//		V(mutex_up_t);
		V_up();

	:: (car_type == down_t) ->
//		P(mutex_down_t);
		P_down();

		down_count++;		
		if
		:: (down_count == 1) ->
//			P(alley_free_t);
			P_alley();
		:: else -> skip;
		fi;

//		V(mutex_down_t);
		V_down();

	:: else -> skip;
	fi
}

inline leave(car_type) {
	if
	:: (car_type == up_t) ->
//		P(mutex_up_t);
		P_up();

		up_count--;		
		if
		:: (up_count == 0) ->
//			V(alley_free_t);
			V_alley();
		:: else -> skip;
		fi;

//		V(mutex_up_t);
		V_up();


	:: (car_type == down_t) ->
//		P(mutex_down_t);
		P_down();

		down_count--;		
		if
		:: (down_count == 0) ->
//			V(alley_free_t);
			V_alley();
		:: else -> skip;
		fi;

//		V(mutex_down_t);
		V_down();
	fi
}

active [nup] proctype car_up(){
do
	::
	 enter(up_t); leave(up_t); break;
/*
	:: leave(up_t);
	:: break;*/
od
}

active [ndown] proctype car_down(){
do
 	:: enter(down_t);
	leave(down_t);	
	break;
od;
skip;
}