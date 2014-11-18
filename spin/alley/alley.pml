// Number of cars headed either upwards or downwards
#define ndown	4
#define nup		4

//The semaphores
short mutex_down 	= 1;
short mutex_up 	= 1;
short alley_free 	= 1;

// Counters
short up_count 	= 0;
short down_count	= 0;

// Used for our assertions
short proof_up_in_alley = 0;
short proof_down_in_alley = 0;


inline P_down() {
atomic { mutex_down > 0;mutex_down--;}
}

inline P_up() {
atomic{mutex_up > 0;mutex_up--;}
}

inline P_alley() {
atomic{alley_free > 0;	alley_free--;}
}


inline V_up() {mutex_up++;}

inline V_down() {mutex_down++;}

inline V_alley() {alley_free++;}

inline enter_up() {
		P_up();

		up_count++;

		if
		:: (up_count == 1) ->
			P_alley();
		:: else -> skip;
		fi;

		proof_up_in_alley++;

		V_up();
}

inline leave_up() {
		P_up();

		proof_up_in_alley--;

		up_count--;
		if
		:: (up_count == 0) ->
			V_alley();
		:: else -> skip;
		fi;


		V_up();
}



inline enter_down() {
		P_down();

		down_count++;
		if
		:: (down_count == 1) ->
			P_alley();
		:: else -> skip;
		fi;

		proof_down_in_alley++;

		V_down();
}



inline leave_down() {
		P_down();

		proof_down_in_alley--;

		down_count--;
		if
		:: (down_count == 0) ->
			V_alley();
		:: else -> skip;
		fi;

		V_down();
}


active [nup] proctype car_up(){
	do::
		enter_up();

		// Inside alley
		assert(proof_down_in_alley == 0 && proof_up_in_alley > 0);

		leave_up();
	od;
}



active [ndown] proctype car_down(){
    	do::
		enter_down();

		// Inside the alley
	    	assert(proof_up_in_alley == 0 && proof_down_in_alley > 0);

		leave_down();
    	od;
}
