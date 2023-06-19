///////////////////////////////////////////////////////////////////////////////
// Name      : monitor.sv : 
// Subject   : Introduction to SystemVerilog [ECE 571]
// Project   : AHB Lite verification
// Authors   : Jonathan Law, Gagan Ganapathy Machiyanda Belliappa, Balaji Rao Vavintaparthi.
// Date      : 11/27/22
// Portland State University
///////////////////////////////////////////////////////////////////////////////

`ifndef include_n
`include "PacketClass.sv"
`endif

class monitor;
PacketClass tr2;
mailbox #(PacketClass) m2;  //mailbox for transfer between monitor to scoreboard
virtual interface AHBInterface.Slave vif;
	
	
function new(mailbox #(PacketClass) m2,virtual interface AHBInterface.Slave vif);

this.m2=m2;
this.vif=vif;
endfunction


function void get_signals(PacketClass tr2);
tr2.HADDR	<= vif.HADDR ;
tr2.HSIZE	<=vif.HSIZE;
tr2.HBURST	<= vif.HBURST;
tr2.HPROT	<= vif.HPROT;
tr2.HTRANS	<= vif.HTRANS;
tr2.HWDATA	<=vif.HWDATA;
tr2.HSEL	<=vif.HSEL;
endfunction

// This is used for sending our transaction from interface to the scoreboard
		
task run();
forever begin
tr2 = new;
@(posedge vif.HCLK);
get_signals(tr2);
@(posedge vif.HCLK);
tr2.HRESP	<= vif.HRESP;
tr2.HREADY	<=vif.HREADY;
tr2.HREADYOUT	<=vif.HREADYOUT;
m2.put(tr2);
$display("Address:%0h Data:%0h",vif.HADDR,vif.HWDATA);
end
			
$display("\n\n----------packet receive from memory---------\n\n");
endtask;

endclass: monitor