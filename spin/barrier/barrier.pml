#define ncars		2

//The semaphores
short mutex 			= 1;
short barrier_incoming 	= 0;
short barrier_leaving 		= 0;

// Counters
short incoming_count 		= 0;
short leaving_count 		= 0;
short threshold		= ncars;

// Testing
short car_rounds[ncars];

inline zero_round_counts() {
	
	short car_index = 0;

	do
	:: 	car_rounds[car_index] = 0;
		car_index++;
		if
		:: (car_index >= ncars) -> break;
		:: else -> skip;
		fi;
	od;
}

// Initialize 
init {
	zero_round_counts();
}

inline V_mutex() {	mutex++;	}
inline P_mutex() {
	atomic {
		mutex > 0;
		mutex--;
	}
}

inline V_incoming() {	barrier_incoming++;	}
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


inline sync(proof_car_no) {
// proof_car_no is only used for proving the correctness

	P_mutex();


	// 1st - all cars must arrive ("incoming")
	incoming_count++;

	// This point is regarded as the end of a round
	car_rounds[proof_car_no]++;

	if
	:: (incoming_count < threshold) ->
		V_mutex();
		P_incoming();
	:: (incoming_count == threshold)	->

				// When the final car leaves for a new round, 
		// all cars should have a round_count of 1	
atomic {
		assert(incoming_count == 2);
		assert(leaving_count == 0);
		assert(car_rounds[0] == 1);
		if
		:: (car_rounds[1] != 1) -> assert(car_rounds[1] == 1);
		:: else -> assert(car_rounds[1] == 1);
		fi;
		car_rounds[0] = 0;
		car_rounds[1] = 0;
}

		free_incoming(incoming_count - 1);
		incoming_count = 0;

		V_mutex();
	:: else -> assert(false);
	fi;


	// 2nd - all cars must leave ("leaving")

	P_mutex();

            	leaving_count++;


	if 
	:: leaving_count < threshold ->
		V_mutex();
		P_leaving();
	:: (leaving_count == threshold) ->
		
		free_leaving(leaving_count - 1);
		leaving_count = 0;
		
		V_mutex();
	:: else -> assert(false);
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

active [ncars] proctype car(){
// _pid is the id of the process - which is equivalent to the id of the car!
assert(_pid >= 1 && _pid <= ncars);

	do ::
		sync(_pid - 1);  //_pid is in the range [1;ncars]
	od;

}

