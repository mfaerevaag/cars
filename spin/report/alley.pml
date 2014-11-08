#define ndown	2
#define nup		2


//The semaphores
short mutex_down 	= 1;
short mutex_up 	= 1;
short alley_free 	= 1;
short up_count 	= 0;
short down_count	= 0;


short entering_count 	= 0;

short up_in_alley = 0;
short down_in_alley = 0;


inline P_down() {
	atomic {
		mutex_down > 0;
		mutex_down--;
	}
}

 
inline P_up() {
	atomic{ 
		mutex_up > 0;
		mutex_up--;
	}
}

inline P_alley() {
	atomic{
		alley_free > 0;
		alley_free--;
	}
}


inline V_up() {
	mutex_up++;
}


inline V_down() {
	mutex_down++;
}

inline V_alley() {
	alley_free++;
}

inline enter_up() {
		P_up();

// Debugging. Proves that only one up-going car is entering at any instant
entering_count++;
assert(entering_count == 1);

		up_count++;

		if
		:: (up_count == 1) ->
			P_alley();
		:: else -> skip;
		fi;

		up_in_alley++;

entering_count--;
		V_up();
}

inline leave_up() {
		P_up();

		up_in_alley--;

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
	
		down_in_alley++;

		V_down();
}



inline leave_down() {
		P_down();

		down_in_alley--;

		down_count--;		
		if
		:: (down_count == 0) ->
			V_alley();
		:: else -> skip;
		fi;


		V_down();
}


active [nup] proctype car_up(){

enter_up();

// Inside alley
assert(down_in_alley == 0);

leave_up();
enter_up();

//assert(down_in_alley == 0);

leave_up();

}



active [ndown] proctype car_down(){

	enter_down();
	
	// Inside the alley

	leave_down();	
	enter_down();

// Inside the alley

	leave_down();	

}

