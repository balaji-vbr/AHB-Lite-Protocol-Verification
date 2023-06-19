///////////////////////////////////////////////////////////////////////////////
// Name      : packet class.sv : 
// Subject   : Introduction to SystemVerilog [ECE 571]
// Project   : AHB Lite verification
// Authors   : Jonathan Law, Gagan Ganapathy Machiyanda Belliappa, Balaji Rao Vavintaparthi.
// Date      : 11/27/22
// Portland State University
///////////////////////////////////////////////////////////////////////////////

class PacketClass;
	rand bit [31:0] Address_rand,Data_rand;
	constraint c {	Address_rand >  32'h00000000;
			Address_rand    <  32'h00000400;
	}
endclass