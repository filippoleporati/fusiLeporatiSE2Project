module taxiModule

sig wString {}
sig posInt { value: Int} {value > 0}
sig boolean {value: Int } {value >= 0 && value <= 1}

abstract sig RegisteredUser
{
	username: one wString,
	email:one wString,
	password:one wString,
	firstname:one wString,
	lastname:one wString,
	phone:lone wString
}

sig TaxiDriver extends RegisteredUser
{
	driverCode: one wString,
	PersonalTaxi: one Taxi,
	drivingLicCode: one wString,
	drivingLicExp: one wString
} 

sig Administrator extends RegisteredUser
{
}


sig Passenger extends RegisteredUser 
{
	PersonalRequest: set Request,
	PersonalReservation: set Reservation
}

sig Taxi
{
	taxiCode: one wString,
	licensePlate: one wString,
	numPass: one posInt,
	taxiArrivalTime: lone posInt,
	available: one boolean,
	presentPosition: lone CityArea
} 

sig Request
{
	requestCode: one wString, 
	numPass: one posInt,
	requestTime: one wString,
	origin: one Position,
	destination: one Position,
	taxi: one Taxi,
	passUsername: one wString,
	active: one boolean
} {
	origin != destination
	taxi.numPass.value >= numPass.value
}

sig Reservation
{
	reservationCode: one wString,
	meetingTime: one wString,
	reservationDate: one wString,
	pickupDate: one wString,
	numPass: one posInt,
	origin: one Position,
	destination: one Position,
	taxi: lone Taxi,
	passUsername: one wString,
	active: one boolean
}{
	origin != destination
	taxi.numPass.value >= numPass.value
}

sig CityArea
{
	areaCode: one wString,
	fieldArea: one posInt,
	numTaxi: one Int,
	minNumTaxi: one Int,
	taxiArea: set Taxi,
	positionInArea: set Position
}
{
	numTaxi = #taxiArea
	numTaxi >= 0
	minNumTaxi >= 0
	fieldArea.value <= 3 && fieldArea.value >= 1
}

sig Position
{
	address: one wString,
	latitude: one posInt,
	longitude: one posInt
}

//----------------NO DUPLICATED IDENTIFICATION CODES---------------------------

fact NoDuplicateId{
no disj td1,td2:TaxiDriver|td1.driverCode=td2.driverCode
no disj t1,t2:Taxi|t1.taxiCode=t2.taxiCode
no disj ca1,ca2:CityArea|ca1.areaCode=ca2.areaCode
no disj res1,res2:Reservation|res1.reservationCode = res2.reservationCode
no disj req1,req2:Request|req1.requestCode = req2.requestCode
no disj t1,t2:Taxi|t1.licensePlate=t2.licensePlate
}

//------------ORIGIN AND DESTINATION MUST BE DIFFERENT--------------------
fact OriginDestinationDifferent{
	all res : Reservation | res.origin != res.destination && all req:Request | req.origin != req.destination
}

assert A_OriginDestinationDifferent{
	all res : Reservation | res.origin != res.destination && all req:Request | req.origin != req.destination
}

check A_OriginDestinationDifferent for 4



//-------------ALL POSITIONS IN AN AREA MUST BE DIFFERENT--------------------
fact AllPositionsAreDifferent{
	all city1: CityArea | some pos1:Position | pos1 in city1.positionInArea implies no pos2:Position | pos2 in  city1.positionInArea && pos1!=pos2 implies pos1.address = pos2.address || pos1.longitude = pos2.longitude && pos1.latitude = pos2.latitude
}

assert A_AllPositionsAreDifferent{
	all city1: CityArea | some pos1:Position | pos1 in city1.positionInArea implies no pos2:Position | pos2 in  city1.positionInArea && pos1!=pos2 implies pos1.address = pos2.address || pos1.longitude = pos2.longitude && pos1.latitude = pos2.latitude
}
check  A_AllPositionsAreDifferent for 4


//---------------ALL TAXIS OF AN AREA MUST BE DIFFERENT-------------------------
fact AllTaxisAreDifferent{
	all city1: CityArea | some taxi1:Taxi | taxi1 in city1.taxiArea implies no taxi2:Taxi | taxi2 in  city1.taxiArea && taxi1!=taxi2 implies taxi1.taxiCode = taxi2.taxiCode
}

assert A_AllTaxisAreDifferent{
	all city1: CityArea | some taxi1:Taxi | taxi1 in city1.taxiArea implies no taxi2:Taxi | taxi2 in  city1.taxiArea && taxi1!=taxi2 implies taxi1.taxiCode = taxi2.taxiCode
}
check  A_AllTaxisAreDifferent for 4

//----------------ALL REQUESTS OF A PASSENGER MUST BE DIFFERENT-------------------
fact AllRequestsAreDifferent{
	all user1: Passenger | some req1:Request | req1 in user1.PersonalRequest implies no req2:Request | req2 in user1.PersonalRequest && req1!=req2 implies req1.requestCode = req2.requestCode
}

assert A_AllRequestsAreDifferent{
	all user1: Passenger | some req1:Request | req1 in user1.PersonalRequest implies no req2:Request | req2 in user1.PersonalRequest && req1!=req2 implies req1.requestCode = req2.requestCode
}
check  A_AllRequestsAreDifferent for 4

//----------------ALL RESERVATIONS OF A PASSENGER MUST BE DIFFERENT-------------------
fact AllReservationAreDifferent{
	all user1: Passenger | some res1:Reservation | res1 in user1.PersonalReservation implies no res2:Reservation | res2 in user1.PersonalReservation && res1!=res2 implies res1.reservationCode = res2.reservationCode
}

assert A_AllReservationAreDifferent{
	all user1: Passenger | some res1:Reservation | res1 in user1.PersonalReservation implies no res2:Reservation | res2 in user1.PersonalReservation && res1!=res2 implies res1.reservationCode = res2.reservationCode
}
check  A_AllReservationAreDifferent for 4

//---------------------- THE SYSTEM HAS ONE ADMINISTRATOR--------------------------
fact OneAdmin {
#Administrator = 1
}

//----------------------NOT TWO TAXI DRIVER WITH THE SAME TAXI---------------------------
fact NoDuplicatedTaxi {
	no disj driver1, driver2: TaxiDriver | driver1.PersonalTaxi = driver2.PersonalTaxi
}

assert A_NoDuplicatedTaxi {
	no disj driver1, driver2: TaxiDriver | driver1.PersonalTaxi = driver2.PersonalTaxi
}
check A_NoDuplicatedTaxi for 4

//-------------------IF A TAXI EXISTS IT MUST BE OWNED BY A TAXI DRIVER---------------
fact NoTaxiWithoutATaxiDriver {
	all taxi1 : Taxi | some driver1: TaxiDriver | driver1.PersonalTaxi = taxi1
}

assert A_NoTaxiWithoutATaxiDriver {
	all taxi1 : Taxi | some driver1: TaxiDriver | driver1.PersonalTaxi = taxi1
}
check A_NoTaxiWithoutATaxiDriver for 4

//----------NOT TWO POSITION WITH SAME ADDRESS----------------------------------

fact NoDuplicatedPosition {
	no disj pos1,pos2:Position|pos1.address = pos2.address || pos1.latitude = pos2.latitude && pos1.longitude = pos2.longitude
}

//---------------------- NO DUPLICATED USERS------------------------------------------------
fact NoDuplicateUser {
    no disj pas1,pas2 : Passenger | pas1.email=pas2.email || pas1.username = pas2.username || pas1.email = pas2.email
} 
assert A_NoDuplicateUser{
	no disj pas1,pas2 : Passenger | pas1.email=pas2.email || pas1.username = pas2.username || pas1.email = pas2.email
}
check A_NoDuplicateUser for 4

//--------- AT LEAST ONE POSITION IN A CITY AREA------------------

fact OnePositionForArea {
	all ca:CityArea | some pos:Position | pos in ca.positionInArea
}

assert A_OnePositionForArea {
	all ca:CityArea | some pos:Position | pos in ca.positionInArea
}
check A_OnePositionForArea for 4 


//--------- NOT SAME POSITION IN TWO DIFFERENT AREAS----------------------------------------------------------
fact OnePositionInOneArea {
	 all p: Position | (some ca:CityArea | p in ca.positionInArea implies no ca':CityArea | ca != ca' implies p in ca'.positionInArea) 
}
assert A_OnePositionInOneArea {
	 all p: Position | (some ca:CityArea | p in ca.positionInArea implies no ca':CityArea | ca != ca' implies p in ca'.positionInArea)
}
check A_OnePositionInOneArea for 4 

//-----------IF TAXI IS AVAILABLE IT MUST BE IN A POSITION-------------------------

fact TaxiOKInPosition {
	all t:Taxi | (t.available.value = 1 implies #t.presentPosition = 1)
}

assert A_TaxiOKInPosition {
	all t:Taxi | (t.available.value = 1 implies #t.presentPosition = 1)
}
check A_TaxiOKInPosition for 4

//----------------FOR ALL PASSENGER AT MOST ONE REQUEST ACTIVATED-----------------------------------
fact AtMostOneActiveReq {
	all p:Passenger | lone r:Request | (r in p.PersonalRequest implies r.active.value = 1)
}

assert A_AtMostOneActiveReq {
	all p:Passenger | lone r:Request | (r in p.PersonalRequest implies r.active.value = 1)
}
check A_AtMostOneActiveReq for 4

//---------------------------- FOR ALL REQUEST IN THE SYSTEM EXISTS A PASSENGER WHO GENERATES THEM--------------------
fact RequestImpliesPassenger {
	all r:Request {some pas:Passenger | r in pas.PersonalRequest}
}

assert A_RequestImpliesPassenger {
	all r:Request {some pas:Passenger | r in pas.PersonalRequest}
}
check A_RequestImpliesPassenger for 4

//--------------------------------- FOR ALL RESERVATION IN THE SYSTEM EXISTS A PASSENGER WHO GENERATES THEM----------------------
fact ReservationImpliesPassenger {
	all r:Reservation {some pas:Passenger | r in pas.PersonalReservation}
}

assert A_ReservationImpliesPassenger {
	all r:Reservation {some pas:Passenger | r in pas.PersonalReservation}
}
check A_ReservationImpliesPassenger for 4

//--------------------------------ACTIVE REQUEST MUST HAVE AN AVAILABLE TAXI------------------------------------------------
fact NoRequestTaxiUnavailable {
	all req:Request { some t:Taxi | req.active.value = 1 implies(t.available.value = 1 && req.taxi = t)  }
}
assert A_NoRequestTaxiUnavailable {
	all req:Request { some t:Taxi | req.active.value = 1 implies(t.available.value = 1 && req.taxi = t)  }
}
check A_NoRequestTaxiUnavailable for 4

//--------------------------------ACTIVE RESERVATION MUST HAVE AN AVAILABLE TAXI------------------------------------------------
fact NoReservationTaxiUnavailable {
	all req:Reservation { some t:Taxi | req.active.value = 1 implies(t.available.value = 1 && req.taxi = t)  }
}
assert A_NoReservationTaxiUnavailable {
	all req:Reservation { some t:Taxi | req.active.value = 1 implies(t.available.value = 1 && req.taxi = t)  }
}
check A_NoReservationTaxiUnavailable for 4

//-------------------------------ACTIVE REQUESTS CANNOT HAVE THE SAME TAXI-----------------------------------

fact TwoRequestDifferentTaxi {
	all req,req':Request { (req.active.value = 1 && req'.active.value = 1)  implies req.taxi != req'.taxi}
}

assert A_TwoRequestDifferentTaxi {
	all req,req':Request { (req.active.value = 1 && req'.active.value = 1)  implies req.taxi != req'.taxi}
}
check A_TwoRequestDifferentTaxi for 4

//-------------------------------ACTIVE RESERVATION CANNOT HAVE THE SAME TAXI-----------------------------------

fact TwoReservationDifferentTaxi {
	all res,res':Reservation { (res.active.value = 1 && res'.active.value = 1)  implies res.taxi != res'.taxi}
}

assert A_TwoReservationDifferentTaxi {
	all res,res':Reservation { (res.active.value = 1 && res'.active.value = 1)  implies res.taxi != res'.taxi}
}
check A_TwoReservationDifferentTaxi for 4

//-------------------- ADD A REQUEST-------------------------------------------------------
pred AddRequestToPass[r:Request,p,p':Passenger] {
	p'.PersonalRequest = p.PersonalRequest + r
}

assert A_CorrectInsertion {
	
	all r:Request, p,p':Passenger | not (r in p.PersonalRequest) && AddRequestToPass[r,p,p']
				 implies ((all r2:Request | (not (r2 in p.PersonalRequest) && r2 in p'.PersonalRequest) implies r2 = r))
														
}
check A_CorrectInsertion for 4


//-------------------- ADD A RESERVATION-----------------
pred AddReservationToPass[r:Reservation,p,p':Passenger] {
	p'.PersonalReservation = p.PersonalReservation + r
}

assert A_AfterInsertOtherResNotChanges {
	
	all r:Reservation, p,p':Passenger | not (r in p.PersonalReservation) && AddReservationToPass[r,p,p']
				 implies ((all r2:Reservation | (not (r2 in p.PersonalReservation) && r2 in p'.PersonalReservation) implies r2 = r))
														
}
check A_AfterInsertOtherResNotChanges for 4


assert A_AddResIncreaseNum {
	
	all r:Reservation, p,p':Passenger | (not (r in p.PersonalReservation) && AddReservationToPass[r,p,p'])
				 implies (#p'.PersonalReservation > 0 )
														
}
check A_AddResIncreaseNum for 4

//-------------------- DELETE A REQUEST-----------------
pred DeleteRequestToPass[r:Request,p,p':Passenger] {
	p'.PersonalRequest = p.PersonalRequest - r
}

assert A_CorrectCancellation {
	
	all r:Request, p,p':Passenger | r in p.PersonalRequest && DeleteRequestToPass[r,p,p']
				 implies ((all r2:Request | (r2 in p.PersonalRequest) && not(r2 in p'.PersonalRequest) implies r2 = r))
														
}
check A_CorrectCancellation for 4

assert A_delUndoesAddRequest {
	all p, p', p'': Passenger, r:Request |
		not(r in p.PersonalRequest) and AddRequestToPass [r, p, p'] and DeleteRequestToPass [r, p', p'']
					implies
							p.PersonalRequest = p''.PersonalRequest
}
check A_delUndoesAddRequest for 4


//-------------------- DELETE A RESERVATION-----------------
pred DeleteReservationToPass[r:Reservation,p,p':Passenger] {
	p'.PersonalReservation = p.PersonalReservation - r
}

assert A_AfterDeleteOtherResNotChanges {
	
	all r:Reservation, p,p':Passenger | r in p.PersonalReservation && DeleteReservationToPass[r,p,p']
				 implies ((all r2:Reservation | (r2 in p.PersonalReservation) && not(r2 in p'.PersonalReservation) implies r2 = r))
														
}
check A_AfterDeleteOtherResNotChanges for 4


assert A_delUndoesAddReservation {
	all p, p', p'': Passenger, r:Reservation |
		not(r in p.PersonalReservation) and AddReservationToPass [r, p, p'] and DeleteReservationToPass [r, p', p'']
					implies
							p.PersonalReservation = p''.PersonalReservation
}
check A_delUndoesAddReservation for 4

//--------------------ASSIGN A TAXI TO A RESERVATION----------------------
pred AssignTaxiToReservation[res,res':Reservation, t:Taxi] {
	res'.taxi = res.taxi + t
}

assert A_AssignTaxiToReservation {
 all res,res':Reservation, t:Taxi |
		(#res.taxi = 0 && AssignTaxiToReservation[res,res',t] && t.numPass.value >= res'.numPass.value)
			 implies (#res'.taxi = 1 && t in res'.taxi )

}
check A_AssignTaxiToReservation for 4


//-------------------------SHOW--------------------------------------------

pred show()
{
#Passenger >= 1
#Request < 3
#Reservation < 3
#Taxi < 3
#CityArea < 3
}
run show for 5

