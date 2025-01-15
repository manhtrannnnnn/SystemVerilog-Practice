//----------------------------------------BASE CLASS----------------------------------------//
class packet #(parameter type DATA_TYPE = int);
    DATA_TYPE length;
    bit [1:0] saddr;
    bit [1:0] daddr;
    DATA_TYPE data[];

    // Constructor
    function new(DATA_TYPE length);
        this.length = length;
    endfunction

    // Randomize data
    task random();
        this.data = new[this.length];
        foreach (this.data[i]) begin
            this.data[i] = $random % 128; 
        end
    endtask

    // Set source and destination 
    function void set_addr(bit [1:0] saddr, bit [1:0] daddr);
        this.saddr = saddr;
        this.daddr = daddr;
        if (this.saddr == this.daddr) begin
            do this.daddr = $random % 4;
            while (this.saddr == this.daddr);
        end
    endfunction

    // Display
    function void display();
        $display("Length: %d, Source Address: %b, Destination Address: %b, Data: %p",
                 this.length, this.saddr, this.daddr, this.data);
    endfunction
endclass

//----------------------------------------MODULE----------------------------------------//
module exe1;

    // Declare packet objects   
    packet #(int) int_packet;
    packet #(bit [7:0]) bit7_packet;
    packet #(bit [3:0]) bit_4packet;

    initial begin
        // Create packet 
        int_packet = new(5);
        bit7_packet = new(4);
        bit_4packet = new(3);

        // Random value
        pkt1.random();
        pkt1.set_addr(2'b00, 2'b01);
        pkt2.random();
        pkt2.set_addr(2'b01, 2'b10);
        pkt3.random();
        pkt3.set_addr(2'b10, 2'b11);

        pkt1.display();
        pkt2.display();
        pkt3.display();

        // Display protected value

    end
endmodule
