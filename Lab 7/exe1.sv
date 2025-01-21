//----------------------------------------BASE CLASS----------------------------------------//
virtual class packet #(parameter type DATA_TYPE = int);

    DATA_TYPE length;
    bit [1:0] saddr;
    bit [1:0] daddr;
    DATA_TYPE data[];

    local int val = 0;
    static int static_ctr  = 0;
    int ctr = 0;

    // Constructor
    function new(DATA_TYPE length);
        this.length = length;
        data = new[this.length];
    endfunction

    // Randomize data (pure virtual, to be implemented in subclasses)
    pure virtual function void random();

    // Set source and destination (pure virtual, to be implemented in subclasses)
    pure virtual function void set_addr(bit [1:0] saddr, bit [1:0] daddr);

    // Set local value
    function void set_val(int val);
        this.val = val;
    endfunction

    // Get local value
    function int get_val();
        return this.val;
    endfunction

    // Static data testing
    function void global_value_testing();
        static_ctr++;
        ctr++;
    endfunction

    // Display packet details (pure virtual, to be implemented in subclasses)
    pure virtual function void display();

endclass

//----------------------------------------Inheritance - SUB CLASS----------------------------------------//
class inherit_packet #(type DATA_TYPE = int) extends packet#(DATA_TYPE);

    // Constructor
    function new(DATA_TYPE length = 10);
        super.new(length);
    endfunction

    // Override random
    function void random();
        foreach (this.data[i]) begin
            this.data[i] = $random % 128; 
        end
    endfunction

    // Override set_addr
    virtual function void set_addr(bit [1:0] saddr, bit [1:0] daddr);
        this.saddr = saddr;
        this.daddr = daddr;
        if (this.saddr == this.daddr) begin
            do this.daddr = $random % 4;
            while (this.saddr == this.daddr);
        end
    endfunction

    // Override display
    function void display();
        $display("[TIME: %0t]Global Value: %0d, Local Value: %0d, Length: %d, Source Address: %b, Destination Address: %b, Data: %p",
                 $time, this.static_ctr, this.ctr, this.length, this.saddr, this.daddr, this.data);
    endfunction
endclass

//----------------------------------------MODULE----------------------------------------//
module exe1;

    // Declare packet objects
    packet int_pkg, bit7_pkg, bit4_pkg;

    // Declare inheritance packet objects
    inherit_packet #(int) int_packet;
    inherit_packet #(int) bit7_packet;
    inherit_packet #(int) bit4_packet;

    // Mailbox and Semaphore
    mailbox pkt_mailbox;
    semaphore arbiter;

    initial begin
        // Initialize objects, mailbox and semaphore
        pkt_mailbox = new();
        arbiter = new(1);
        int_packet = new(5); 
        bit7_packet = new(4);
        bit4_packet = new(3);
        int_pkg = int_packet;
        bit7_pkg = bit7_packet;
        bit4_pkg = bit4_packet;

        // Declare int parameter packet
        int_pkg.random();
        int_pkg.set_addr(2'b10, 2'b01);
        int_pkg.global_value_testing();
        pkt_mailbox.put(int_pkg); 

        // Declare 8-bit parameter packet
        bit7_pkg.random();
        bit7_pkg.set_addr(2'b01, 2'b10);
        bit7_pkg.global_value_testing();
        pkt_mailbox.put(bit7_pkg);

        // Declare 4-bit parameter packet
        bit4_pkg.random();
        bit4_pkg.set_addr(2'b11, 2'b11); // Same saddr and daddr
        bit4_pkg.global_value_testing();
        pkt_mailbox.put(bit4_pkg);

        // Semaphore arbiter for accessing packets
        fork
            process_packet();
            process_packet();
            process_packet();
        join
    end

    // Task to process packets
    task process_packet();
        packet pkt;
        arbiter.get(1); 
        pkt_mailbox.get(pkt); 
        pkt.display(); 
        #5;
        arbiter.put(1); 
    endtask
endmodule
