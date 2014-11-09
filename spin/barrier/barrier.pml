#define ncars		4


//The semaphores
short mutex 			= 1;
short barrier_incoming 	= 0;
short barrier_leaving 		= 0;

// Counters
short incoming_count 		= 0;
short leaving_count 		= 0;
short threshold		= ncars;

// Testing
short max_rounds 		= 0;

inline V_mutex() {	mutex++;	}
inline P_mutex() {
	atomic {
		mutex > 0;
		mutex--;
	}
}


inline P_incoming() {
	atomic{ 
		barrier_incoming > 0;
		barrier_incoming--;
	}
}

inline V_leaving(){	barrier_leaving++;	}
inline P_leaving() {
	atomic{
		barrier_leaving > 0;
		barrier_leaving--;
	}
}


inline sync() {
	P_mutex();



	// 1st - all cars must arrive ("incoming")
	incoming_count++;

	if
	:: (incoming_count < threshold) ->
		V_mutex();
		P_incoming();
	:: else	->
		free_incoming(incoming_count - 1);
		incoming_count = 0;
		V_mutex();
	fi;
	


	// 2nd - all cars must leave ("leaving")

	P_mutex();
            	leaving_count++;

	if 
	:: leaving_count < threshold ->
		V_mutex();
		P_leaving();
	:: else ->
		free_leaving(leaving_count - 1);
		leaving_count = 0;
		V_mutex();
	fi;


}


inline free_incoming(n) {
	barrier_incoming = barrier_incoming + n;
}

inline free_leaving(n) {
	barrier_leaving = barrier_leaving + n;
}

// BEFORE BARRIER
// BEFORE BARRIER
// BEFORE BARRIER


inline count_round() {
	atomic {
		round_count++;

		if
		:: round_count > max_rounds -> max_rounds = round_count;
		:: else -> skip;
		fi;
	}
}

active [ncars] proctype car_up(){
	short round_count = 0;

	sync();
	count_round();
	assert ( round_count == max_rounds);
	assert(max_rounds == 1);
	assert(round_count == 1);


	sync();
	count_round();
	assert ( round_count == max_rounds);
	assert(max_rounds == 2);
	assert(round_count == 2);


	sync();
	count_round();
	assert ( round_count == max_rounds);
	assert(max_rounds == 3);
	assert(round_count == 3);



	sync();
	count_round();
	assert ( round_count == max_rounds);
	assert(max_rounds == 4);
	assert(round_count == 4);


}
