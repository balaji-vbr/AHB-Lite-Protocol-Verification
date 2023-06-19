///////////////////////////////////////////////////////////////////////////////
// Name      : driver.sv : 
// Subject   : Introduction to SystemVerilog [ECE 571]
// Project   : AHB Lite verification
// Authors   : Jonathan Law, Gagan Ganapathy Machiyanda Belliappa, Balaji Rao Vavintaparthi.
// Date      : 11/27/22
// Portland State University
///////////////////////////////////////////////////////////////////////////////

`ifndef include_n
`include "PacketClass.sv"
`endif
class driver;
PacketClass tr;
mailbox #(PacketClass) m1; //mailbox for transfer between generator to driver
virtual interface AHBInterface.Master vif;
	

function new(mailbox #(PacketClass) m1,virtual interface AHBInterface.Master vif);

this.m1=m1;
this.vif=vif;
endfunction

task run();

forever begin
tr=new;
m1.get(tr);
vif.HREADYOUT=1;
vif.HRESP=0;
if(vif.HREADYOUT && !vif.HRESP)begin		
vif.HSEL 	<= tr.HSEL ;
vif.HADDR	<= tr.HADDR;
vif.HWDATA	<= tr.HWDATA;
vif.HWRITE	<= tr.HWRITE;
vif.HSIZE	<= tr.HSIZE;
vif.HBURST 	<= tr.HBURST;
vif.HPROT	<= tr.HPROT;
vif.HTRANS	<= tr.HTRANS;
vif.HREADY	<= tr.HREADY;
$display("Address: %0h Data: %0h",vif.HADDR,vif.HWDATA);
end
		
end
endtask;
   	

endclass: driver