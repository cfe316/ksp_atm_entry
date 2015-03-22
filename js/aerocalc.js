// KSP Aerobraking Calculator
$(document).ready(function() {
(function() {

	this.mkPlanet = function(Rmin, Ratm, SOI, mu, H0, P0, Trot) {
		return {
			Rmin: Rmin,	// Equatorial Radius (m)
			Ratm: Ratm+Rmin,	// Atmospheric Height (m) // helps simplify calculations
			SOI: SOI,	// Sphere of influence (m)
			mu: mu,	// Grav. parameter (m3/s2) // kerbal constant
			H0: H0,	// Scale height of atmosphere (m) // P falls off by 1/e for each H0
			P0: P0,	// Pressure at zero altitude (atm)
			Trot: Trot	// Sidereal Rotation Period (s)
		};
	};

	this.Planets = {
		Eve: mkPlanet(700000,96708.574,85109365,8.1717302e12,7000,5,80500),
		Kerbin: mkPlanet(600000,69077.553,84159286,3.5316e12,5000,1,21600),
		Duna: mkPlanet(320000,41446.532,47921949,301363210000,3000,0.2,65517.859),
		Jool: mkPlanet(6000000,138155.11,2455985200,2.82528e14,10000,15,36000),
		Laythe: mkPlanet(500000,55262.042,3723645.8,1.962e12,4000,0.8,52980.879)
	};

	this.timeString = function(s) {
		var MINUTES = 60;
		var HOURS = 60 * MINUTES;
		var DAYS = 6 * HOURS;
		var myD = Math.floor( s / DAYS );
		var sRemainder = s % DAYS;
		var myH = Math.floor( sRemainder / HOURS);
		sRemainder %= HOURS;
		var myM = Math.floor( sRemainder / MINUTES);
		sRemainder %= MINUTES;
		var ts = sRemainder.toFixed(0) + "s"; //time string
		if (myM > 0 || myH > 0 || myD > 0) { ts = myM + "m " + ts; }
		if (           myH > 0 || myD > 0) { ts = myH + "h " + ts; }
		if (                      myD > 0) { ts = myD + "d " + ts; }
		
		return ts;
	};

	// An extenstion of parseFloat to allow (optional) use of units.
	// Assumes meters if no units are given.
	this.parseUnitFloat = function(v) {
		var v = v.toLowerCase();
		var value = parseFloat(v);
		if (v.indexOf("mm") !== -1) {
			return value * 1000000;
		} else if (v.indexOf("km") !== -1) {
			return value * 1000;
		} else {
			return value;
		}
	};

	this.sign = function(x) { return x > 0 ? 1 : x < 0 ? -1 : 0; }

	// Simple 2D vector math implementation
	this.vmult = function( k, v ) {
		var ret = new Array();
		for (var i = 0; i < v.length; ++i) {ret[i] = v[i]*k;}
		return ret;
	};
	this.vsum = function() {
		var ret = new Array();
		for (var i = 0; i < arguments[0].length; ++i) {
			ret[i] = 0;
			for (var j = 0; j < arguments.length; ++j) {
				ret[i] += arguments[j][i];
			}
		}
		return ret;
	};
	this.vdiff = function( a, b ) {
		var ret = new Array();
		for (var i = 0; i < a.length; ++i) {ret[i] = a[i] - b[i];}
		return ret;
	};
	this.vnorm = function( v ) {
		var norm = 0;
		for (var i = 0; i < v.length; ++i) {norm += v[i]*v[i];}
		return Math.sqrt(norm);
	};
	this.vdot = function( a, b ) {
		var ret = 0;
		for (var i = 0; i < a.length; ++i) ret += a[i]*b[i];
		return ret;
	};
	this.vcross2d = function( a, b ) {	// Cross [a0 a1 0] with [b0 b1 0]
		return a[0]*b[1] - a[1]*b[0];
	};
	this.vec2 = function( x, y ) {
		return [x, y];
	};
	//
	// because IE still doesn't implement these
	this.sinh = function(x) { var p = Math.exp(x); var n = 1/p; return (p-n)/2; };
	this.arctanh = function(x) { return 0.5 * Math.log((1 + x)/(1 - x)); };

	//--------------------------------------------------------------------

	// Physics integrator
	// Velocity-Verlet with Velocity-dependent forces
	// Terminates once atmosphere is breached OR if impact occurs.
	this.integrate_path = function(cart, d, Planet, orbitDir) {
		var t = 0, r = cart.r, v = cart.v;
		var dt = 0.1;
		var Fd = drag_force(d, 1, 1, Planet, orbitDir); // The 1 is because Area and Mass are not relevant to the drag model: only drag coefficient.
		var Fg = gravity_force(1, Planet);

		var adrag = function(rin, vin) { return Fd(rin, vin); }; // acceleration = force because mass is 1.
		var agrav = function(rin) { return Fg(rin); };           // acceleration = force because mass is 1.
		var a = function(rin, vin) { var ad = adrag(rin, vin); var ag = agrav(rin); return vsum(agrav(rin), adrag(rin, vin)); };

		var curr_ad = -1, maxDrag = -1, hMaxDrag = -1, tMaxDrag = -1;

		var CHUTE_SAFE_V = 250;
		var chuteSafeVReached = false;
		var hChuteSafe = -1, tChuteSafe = -1;

		firststep = true;

		var rold, vold, vest, a_t;

		//While in atmosphere and not landed
		while (firststep || (vnorm(r) <= Planet.Ratm && vnorm(r) >= Planet.Rmin)) {
			rold = r;
			vold = v;
			a_t = a(rold, vold);
			r = vsum(rold, vmult(dt, vold), vmult(0.5*dt*dt, a_t));
			vest = vsum(vold, vmult(0.5*dt, vsum(a_t,a(r,vsum(vold,vmult(dt,a_t))))));
			v = vsum(vold, vmult(0.5*dt,vsum(a_t,a(r,vest))));

			firststep = false;

			curr_ad = vnorm(adrag(r, v));
			if(curr_ad > maxDrag){
				maxDrag = curr_ad;
				hMaxDrag = vnorm(r);
				tMaxDrag = t;
			}

			if(vnorm(v) < CHUTE_SAFE_V && chuteSafeVReached == false){
				chuteSafeVReached = true;
				hChuteSafe = vnorm(r);
				tChuteSafe = t;
			}

			t = t + dt;
		}
		return {hMaxDrag: hMaxDrag, tMaxDrag: tMaxDrag, hChuteSafe: hChuteSafe, tChuteSafe: tChuteSafe, rf: r, vf: v, tf: t};
	};

	
	// Get orbit parameters in the plane of orbit
	// r and v are vectors
	this.get_orbit_params = function( r, v, Planet ) {
		var ep = vdot(v,v)/2 - Planet.mu/vnorm(r); // sp. orbital energy
		var hmag = vcross2d(r,v); // sp. angular momentum
		var ec = Math.sqrt(1+2*ep*hmag*hmag/Planet.mu/Planet.mu); // eccentricity
		var a = -Planet.mu/(2*ep); // semi-major axis
		var rpe = -a*(ec-1); // Periapsis distance
		var rap = (1+ec)*a; // Apoapsis distance
		var rn = vnorm(r);
		var nu = Math.acos((a * (1 - ec*ec) - rn) / ( ec * rn) );

		return {ep: ep, ec: ec, a: a, hmag: hmag, rpe: rpe, rap: rap, nu: nu};
	};

	// Return a function describing the drag force while in atmosphere: 
	// The function definition depends on whether the user has indicated a prograde or retrograde orbit, or to ignore the planet's rotation.
	this.drag_force = function(d, m, A, Planet, orbitDir) {
		// Need to consider orbit direction!
		var Kp = 1.2230948554874*0.008,
			braking_functions = {
				"prograde": function(r,v) {return vdiff(v, vmult(-1,[-2.0*Math.PI/Planet.Trot*r[1], 2.0*Math.PI/Planet.Trot*r[0]]))},
				"retrograde": function(r,v) {return vdiff(v, vmult(1,[-2.0*Math.PI/Planet.Trot*r[1], 2.0*Math.PI/Planet.Trot*r[0]]))},
				"ignore": function(r,v) {return v;}
			},
			v_surface = braking_functions[orbitDir]; // velocity relative to the surface
		return function(r,v){
				return vmult(-0.5*Kp*Planet.P0*Math.exp((Planet.Rmin-vnorm(r))/Planet.H0) * vnorm(v_surface(r,v))*d*m*A, v_surface(r,v)); // drag
			};
	};

	// Returns a function describing a (directional) gravity force as a function of vector r.
	this.gravity_force = function(m, Planet) {
		return function(r){
			return vmult(-m*Planet.mu/Math.pow(vnorm(r),3), r);
		};
	};

	/*
	this.calc1 = function(dist, vx, vy, d, Planet, orbitDir) {
		var r0 = [dist, 0],
			v0 = [vx, vy],
			dt = 1,
			m = 1,
			A = 1;

		var rap_out = 0;

		var p1 = get_orbit_params( r0, v0, Planet );

		if (p1.rpe > Planet.Ratm) {
			if (p1.rap < Planet.SOI) {
				// Initial stable, no atmosphere entry
				rap_out = p1.rap;
				return rap_out;
			} else {
				// Initial ep<0 SOI escape
				rap_out = Planet.SOI+1;
				return rap_out;
			}
		}
		// If we've made it this far, we're hitting the atmosphere without guarantee of impact!
		//console.log(Planet);
		// Angle from periapsis at which we contact the atmosphere.
		var theta_contact = Math.acos((1/p1.ec)*(p1.a*(1-p1.ec*p1.ec)/Planet.Ratm-1));

		// Magnitude of velocity when contacting atmosphere
		var vcontact_mag = Math.sqrt(2*(p1.ep+Planet.mu/Planet.Ratm));

		// Use conservation of angular momentum to find angle between velocity and radial position
		var theta_1 = Math.asin(p1.hmag/(Planet.Ratm*vcontact_mag));

		var rcontact = vmult(Planet.Ratm, [Math.cos(theta_contact), Math.sin(theta_contact)]);

		// The sines and cosines here have been chosen to give the velocity as [vr, vtheta]
		var vcontact = vmult(vcontact_mag, [-Math.cos(theta_1+theta_contact), -Math.sin(theta_1+theta_contact)]);

		// F is a function.
		var F = in_atmo_force( d, m, A, Planet, orbitDir );

		// Integrate path in atmosphere.
		var rvt = integrate_path(F, m, rcontact, vcontact, dt, Planet);

		if (vnorm(rvt.rf) >= Planet.Rmin) {// If not, we've impacted!
			var p2 = get_orbit_params(rvt.rf, rvt.vf, Planet);
			if (p2.ep < 0) {
				rap_out = (1+p2.ec)*p2.a;	// Tentative apoapse distance
				if (rap_out > Planet.SOI) { // Post aerobrake SOI escape!
					rap_out = Planet.SOI+1;
					return rap_out;
				}
				//console.log('Capture!');
			} else {
				rap_out = Planet.SOI+1;	// Parabolic or hyperbolic escape
				//console.log('Escape!');
				return rap_out;
			}
		} else {
			// Impact!
			//console.log('Impact!');
			rap_out = Planet.Rmin;
			return rap_out;
		}
		final_orbit_params = get_orbit_params(rvt.rf, rvt.vf, Planet);
		return rap_out;
	};*/

	// assumes argument of periapsis is zero
	this.cartesianFromKeplerian = function(kep, Planet) {
		var nu = kep.nu;
		var a = kep.a;
		var ec = kep.ec;
		var dist = a * (1 - ec*ec) / (1 + ec * Math.cos(nu));
		var r = [ dist * Math.cos(nu), dist * Math.sin(nu) ];
		var vmag = Math.sqrt(Planet.mu/( a * (1 - ec*ec)));
		var v = [ - vmag * Math.sin(nu), vmag * ( ec + Math.cos(nu)) ];

		return {r: r, v: v};
	}

	// Compute orbital parameters from user input. r (radius mag.) and v (velocity mag.) are scalars. rpe is radius of periapsis.
	this.keplerianFromRVP = function(r, v, rpe, Planet) {
		var ep = v*v/2 - Planet.mu/r; // sp. orbital energy
		var a = -Planet.mu/(2*ep); // semi-major axis
		var ec = 1 - rpe/a; //eccentricity
		var rap = (1+ec)*a; // Apoapsis distance
		// current true anomaly nu (assuming the rocket is on the way down).
		var nu = - Math.acos((a * (1 - ec*ec) - r) / ( ec * r) );

		return {ep: ep, ec: ec, a: a, rpe: rpe, rap: rap, nu: nu};
	};

	this.nuOfAtmosphereEntry = function(kep, Planet) {
		//Assuming the rocket is on the way down...
		var Ratm = Planet.Ratm;
		var a = kep.a;
		var ec = kep.ec;
		var nu = - Math.acos((a * (1 - ec*ec) - Ratm) / ( ec * Ratm) );
		return nu;
	};


	// get mean anomaly from eccentric anomaly
	this.MeanAnomFromEccAnom = function(kep, EA) {
		var MA;
		if ( kep.ec < 1 ) {
			MA = EA - kep.ec * Math.sin(EA);
		} else {
			MA = kep.ec * sinh(EA) - EA; 
		}
		return MA;
	};

	// For elliptic cases from wikipedia.org/wiki/Eccentric_anomaly
	// For hyperbolic case from http://mmae.iit.edu/~mpeet/Classes/MMAE441/Spacecraft/441Lecture17.pdf
	this.EccAnomFromTrueAnom = function(kep, nu) {
		var EA;
		var ec = kep.ec;
		if ( kep.ec < 1 ) {
			EA = 2 * Math.atan(Math.tan(nu/2) * Math.sqrt((1-ec)/(1+ec)));
		} else {
			EA = arctanh(Math.sqrt((ec-1)/(ec+1)) * Math.tan(nu/2.0));
		}
		return EA;
	};

	// Composition of the two functions
	this.MeanAnomFromTrueAnom = function(kep, nu){
		return MeanAnomFromEccAnom(kep, EccAnomFromTrueAnom(kep, nu));
	};

	this.timeBetweenTrueAnomalies = function(kep, nu1, nu2, Planet) {
		var MA1 = MeanAnomFromTrueAnom(kep, nu1); // get Mean anomalies of each point
		var MA2 = MeanAnomFromTrueAnom(kep, nu2); 
		var mu = Planet.mu;
		var a = Math.abs(kep.a);
		var perFac = Math.sqrt(Math.pow(a,3) / mu); // sqrt(a^3/mu) is like a period without 2 pi.
		return perFac * Math.abs(MA1 - MA2);
	};

	this.timeToAtmEntry = function(r, v, rpe, Planet) {
		var kep = keplerianFromRVP(r, v, rpe, Planet);
		var nu1 = kep.nu;
		var nu2 = nuOfAtmosphereEntry(kep, Planet);
		var timeToAtm = timeBetweenTrueAnomalies(kep, nu1, nu2, Planet);
		return timeToAtm;
	};

	this.apoCircDeltaV = function(kep, Planet) {
		var rap = kep.rap; // radius of apoapsis
		var a = kep.a;
		var vap = Math.sqrt( Planet.mu * ( 2 / rap - 1 / a ));
		var vcirc = Math.sqrt(Planet.mu / rap);
		return vcirc - vap;
	}

	// Main function
	// r is scalar (distance from centre of planet)
	// v is scalar (magnitude of orbital velocity)
	// rpe is scalar (periapsis distance)
	// We search for a constant-velocity solution to this problem.
	this.computeTrajectory = function( r, v, rpe, d, Planet, orbitDir ) {

		if (rpe > Planet.Ratm) {
			$('#inputAlt,#inputVel,#inputPE,#outputType').parent().parent().addClass('error');
			$('#outputType').val('No atmosphere entry!');
			return;
		}
		
		var timeToAtm = timeToAtmEntry(r, v, rpe, Planet);

		if (isNaN(timeToAtm)) {
			$('#inputAlt,#inputVel,#inputPE,#outputType').parent().parent().addClass('error');
			$('#outputType').val('Error: Inconsistent Input');
			return;
		}

		var timeToAtmString = timeString(timeToAtm);
		$('#outputAtmEntryTime').val(timeToAtmString);

		var kep = keplerianFromRVP(r, v, rpe, Planet);
		kep.nu = nuOfAtmosphereEntry(kep, Planet);
		atmEntryCoords = cartesianFromKeplerian(kep, Planet);
		eventHistory = integrate_path(atmEntryCoords, d, Planet, orbitDir);

		var rf = eventHistory.rf;
		if( vnorm(rf) <= Planet.Rmin) {
			var tLand = timeString(timeToAtm + eventHistory.tf);
			var tMaxDrag = timeString(timeToAtm + eventHistory.tMaxDrag);
			var hMaxDrag = eventHistory.hMaxDrag - Planet.Rmin;
			var tChuteSafe = timeString(timeToAtm + eventHistory.tChuteSafe); 
			var hChuteSafe = eventHistory.hChuteSafe - Planet.Rmin;

			$('#outputType').val("Landing");
			$('#outputMaxQTime').val(tMaxDrag);
			$('#outputMaxQAlt').val((hMaxDrag).toFixed(0) + " m");
			$('#outputChuteTime').val(tChuteSafe);
			$('#outputChuteAlt').val((hChuteSafe).toFixed(0) + " m");
			$('#output0mTime').val(tLand);
		} else { // The craft does not land ... it is only aerobraking.
			var tEsc = eventHistory.tf + timeToAtm;
			var tEscString = timeString(tEsc);

			// get info on final keplerian orbit
			kepFinal = get_orbit_params(rf, eventHistory.vf, Planet);


			// If after aerobraking the craft is in an elliptical orbit
			if ( kepFinal.ec < 1 ) {
				$('#outputType').val("Aerobraking - Captured");
				$('#outputApoapsis').val(((kepFinal.rap - Planet.Rmin)/1000).toFixed(0) + " km");
				$('#outputPeriapsis').val(((kepFinal.rpe - Planet.Rmin)/1000).toFixed(0) + " km");

				var reachApoTime = timeBetweenTrueAnomalies(kepFinal, kepFinal.nu, 3.14159, Planet) + tEsc;
				var apoCircDV = apoCircDeltaV(kepFinal, Planet);
				$('#outputApoTime').val(timeString(reachApoTime));
				$('#outputApoV').val((Math.sqrt(Planet.mu * ( 2 / kepFinal.rap - 1 / kepFinal.a))).toFixed(1) + " m/s");
				$('#outputApoCircDV').val( (apoCircDV).toFixed(1) +" m/s");
			} else {
				$('#outputType').val("Aerobraking - Escaping");
				$('#outputApoapsis').val("n/a");
				$('#outputPeriapsis').val("n/a");
				$('#outputApoTime').val("n/a");
				$('#outputApoV').val("n/a");
				$('#outputApoCircDV').val("n/a");
			}

			$('#outputAtmExitTime').val(tEscString);
			$('#outputEccentricity').val((kepFinal.ec).toFixed(3));
		}
	};
	var that = this;

	$('#go').click(function() {

		$('#inputAlt,#inputVel,#inputPE,#outputType').parent().parent().removeClass('error');
		$('#outputAtmEntryTime').val("");
		$('#outputType').val("");
		$('#outputMaxQTime').val("");
		$('#outputMaxQAlt').val("");
		$('#outputChuteTime').val("");
		$('#outputChuteAlt').val("");
		$('#output0mTime').val("");
		$('#outputAtmExitTime').val("");
		$('#outputApoapsis').val("");
		$('#outputPeriapsis').val("");
		$('#outputEccentricity').val("");
		$('#outputApoTime').val("");
		$('#outputApoV').val("");
		$('#outputApoCircDV').val("");

		var Planet = that.Planets[$('#inputBody').val()];
		var r = parseUnitFloat($('#inputAlt').val(), 10)+Planet.Rmin;	// input altitude
		var v = parseFloat($('#inputVel').val(), 10);			// input velocity
		var pe = parseUnitFloat($('#inputPE').val(), 10)+Planet.Rmin;	// input periapsis
		var orbitDir = $('input[name=inputDir]:radio:checked').val();	// orbit direction (pro/retrograde)
		var d = parseFloat($('#inputD').val(), 10);			// Drag coefficient

		computeTrajectory(r,v,pe,d,Planet,orbitDir);
	});
	return this;
})();
});
