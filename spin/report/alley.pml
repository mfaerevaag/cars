#define ndown	4	/* no. of up-cars */
#define nup		4	/* no. of down-cars */

mtype = { mutex_up_t, mutex_down_t, alley_free_t}
mtype = { up_t, down_t }

//The semaphores
short mutex_down 	= 0;
short mutex_up 	= 0;
short alley_free 	= 0;

inline V(sema_selector) {
	if
	:: (sema_selector == mutex_down_t) -> mutex_down++;
	:: (sema_selector == mutex_up_t) -> mutex_up++;
	:: (sema_selector == alley_free_t) -> alley_free++;
	fi
}

inline P(sema_selector) {
	skip
}

inline enter(car_type) {
	if
	:: (car_type == up_t) -> skip //TODO
		
	:: (car_type == down_t) -> skip //TODO
	fi
}

active [nup] proctype car_up(){
do
 	:: enter(up_t)
od
}

active [ndown] proctype car_down(){
do
 	:: enter(down_t)
od
}


